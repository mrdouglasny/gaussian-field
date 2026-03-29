# MeasurableSpace Diamond: gaussian-field vs bochner

## Problem

gaussian-field and bochner both define `MeasurableSpace (WeakDual ℝ E)`:

- **gaussian-field** (`GaussianField/Construction.lean`):
  ```lean
  instance instMeasurableSpaceConfiguration : MeasurableSpace (Configuration E) :=
    MeasurableSpace.comap (fun ω f => ω f) MeasurableSpace.pi
  ```

- **bochner** (`Minlos/NuclearSpace.lean`):
  ```lean
  instance : MeasurableSpace (WeakDual ℝ E) :=
    ⨆ (f : E), (borel ℝ).comap (fun l => l f)
  ```

These are mathematically the SAME σ-algebra (pi = ⨆ of coordinates), but
not definitionally equal in Lean. Importing both causes typeclass synthesis
failures ("synthesized type class instance is not definitionally equal").

## Impact

This blocks using `minlos_uniqueness` (from bochner, 0 sorries) in pphi2
to prove Gaussian measure uniqueness from covariance. The mathematical
proof is complete — only the typeclass bridge is missing.

## Fix

One project should import the other's `MeasurableSpace` instance instead of
defining its own. Options:

1. **bochner imports gaussian-field's** `instMeasurableSpaceConfiguration`
   - Pro: gaussian-field is the more fundamental dependency
   - Con: bochner would depend on gaussian-field (currently independent)

2. **gaussian-field imports bochner's** definition
   - Pro: bochner's definition is simpler (⨆ of comap)
   - Con: adds dependency

3. **Both import from Mathlib** (if Mathlib adds a canonical cylindrical σ-algebra)
   - Pro: cleanest long-term
   - Con: requires Mathlib PR

4. **Prove equality and transport** (in pphi2)
   - Pro: no cross-repo changes
   - Con: needs `comap_iSup` identity + measure transport lemmas

## Proof that they're equal

```
comap (fun ω f => ω f) MeasurableSpace.pi
= comap (fun ω f => ω f) (⨆ f, (borel ℝ).comap (proj f))
= ⨆ f, comap (fun ω f' => ω f') ((borel ℝ).comap (proj f))
= ⨆ f, (borel ℝ).comap (proj f ∘ (fun ω f' => ω f'))
= ⨆ f, (borel ℝ).comap (fun ω => ω f)
```
