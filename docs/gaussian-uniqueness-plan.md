# Plan: Gaussian Measure Uniqueness via Minlos

## Goal

Prove that two probability measures on `Configuration E` with the same
characteristic functional are equal. This provides the uniqueness half of
the Bochner-Minlos theorem for Gaussian measures on nuclear spaces.

**Target theorem** (to be exposed from gaussian-field):
```lean
theorem configuration_measure_unique_of_charFun
    [DyninMityaginSpace E] [SeparableSpace E] [Nonempty E]
    (μ₁ μ₂ : ProbabilityMeasure (Configuration E))
    (h : ∀ f : E, ∫ ω, exp (I * ω f) ∂μ₁ = ∫ ω, exp (I * ω f) ∂μ₂) :
    μ₁ = μ₂
```

## Consumer: pphi2

The axiom `gaussian_measure_unique_of_covariance` in
`Pphi2/TorusContinuumLimit/TorusGaussianLimit.lean` needs this for
`E = TorusTestFunction L`. The pphi2 proof converts the MGF hypotheses
to matching characteristic functionals (using `eqOn_complexMGF_of_mgf`),
then calls this uniqueness theorem.

## Dependencies

Add **bochner** (`github.com/mrdouglasny/bochner`) as a lake dependency.
Both projects already pin the same Mathlib commit (`6dc31c1...`).

```lean
-- In lakefile.lean:
require BochnerMinlos from git
  "https://github.com/mrdouglasny/bochner.git"
```

The key import is `Minlos.Main` which provides:
```lean
theorem minlos_uniqueness
    [IsHilbertNuclear E] [SeparableSpace E] [Nonempty E]
    {Φ : E → ℂ} (hΦ_cont : Continuous Φ)
    (hΦ_pd : IsPositiveDefinite Φ) (hΦ_norm : Φ 0 = 1)
    {μ₁ μ₂ : ProbabilityMeasure (WeakDual ℝ E)}
    (h₁ : ∀ f, ∫ ω, exp (I * (ω f)) ∂μ₁.toMeasure = Φ f)
    (h₂ : ∀ f, ∫ ω, exp (I * (ω f)) ∂μ₂.toMeasure = Φ f) :
    μ₁ = μ₂
```

## Implementation: new file `GaussianField/Uniqueness.lean`

Estimated ~80 lines. Four steps:

### Step 1: Bridge typeclasses (~15 lines)

gaussian-field's `NuclearSpace` and bochner's `IsNuclear` are the same
Pietsch nuclear dominance condition (class vs def, `‖f n x‖` vs `|f n x|`).
The bridge is:

```
DyninMityaginSpace E        -- gaussian-field (typeclass)
  → NuclearSpace E           -- gaussian-field (proved)
  → IsNuclear E              -- bochner (trivial conversion: same predicate)
  → IsHilbertNuclear E       -- bochner (proved in PietschBridge.lean)
```

```lean
instance instIsHilbertNuclear [DyninMityaginSpace E] : IsHilbertNuclear E :=
  isHilbertNuclear_of_nuclear <| by
    intro p hp
    obtain ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bnd, hdom⟩ :=
      NuclearSpace.nuclear_dominance p hp
    exact ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum,
      fun n x => (abs_le.mpr ⟨by linarith [hf_bnd n x], le_of_eq (abs_of_nonneg ..)|>..).le,
      fun x => by convert hdom x using 1; congr 1; ext n; rw [abs_of_nonneg ..]⟩
```

### Step 2: CF properties (~30 lines)

Define `Φ f := ∫ ω, exp (I * ω f) ∂μ₁` (the CF of μ₁). Then:

- **Φ(0) = 1**: `∫ exp(I * 0) dμ₁ = ∫ 1 dμ₁ = 1` (~5 lines)
- **IsPositiveDefinite Φ**: Standard argument
  `∑ᵢⱼ c̄ᵢcⱼ Φ(fⱼ-fᵢ) = ∫ |∑ᵢ cᵢ exp(I * ω fᵢ)|² dμ ≥ 0`
  (~15 lines, swap sum/integral + recognize norm squared)
- **Continuous Φ**: DCT with bound `‖exp(I * ω f)‖ = 1` + continuity
  of `f ↦ ω f` in the weak-* topology (~10 lines)

### Step 3: Measure ↔ ProbabilityMeasure glue (~10 lines)

`minlos_uniqueness` uses `ProbabilityMeasure`, our API uses `Measure` with
`[IsProbabilityMeasure]`. Convert via `⟨μ, inferInstance⟩` and `.toMeasure`.

### Step 4: Assembly (~10 lines)

```lean
theorem configuration_measure_unique_of_charFun ... :=
  -- Define Φ as CF of μ₁
  let Φ : E → ℂ := fun f => ∫ ω, exp (I * ω f) ∂μ₁
  -- h says Φ = CF of μ₂
  -- Apply minlos_uniqueness with Φ, its properties, and h
  minlos_uniqueness hΦ_cont hΦ_pd hΦ_norm (fun f => rfl) (fun f => (h f).symm)
```

## Current status

**Axiom placeholder added** (`GaussianField/Properties.lean`):

```lean
axiom measure_unique_of_charFun
    (T : E →L[ℝ] H)
    (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [hprob : @IsProbabilityMeasure _ instMeasurableSpaceConfiguration μ]
    (hcharFun : ∀ f : E,
      ∫ ω : Configuration E,
        Complex.exp (Complex.I * ↑(ω f)) ∂μ =
      Complex.exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ (T f) (T f)))) :
    μ = measure T
```

This axiom states: any probability measure on `Configuration E` with the
Gaussian characteristic functional `exp(-½‖Tf‖²)` must equal `measure T`.
It will be proved by importing the Minlos theorem from the bochner project
following the steps above.

## Verification

After implementation, verify with `lean_verify` that the theorem uses only
standard Lean axioms + the existing gaussian-field/bochner axiom sets.
