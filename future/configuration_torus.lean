/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Future: Polish and Borel instances for Configuration(Torus)

These statements are NOT active axioms. They are parked here as future
proof targets. The functionality they were intended for (Prokhorov's theorem
on Configuration spaces) is now provided by `prokhorov_configuration` in
`GaussianField/ConfigurationEmbedding.lean`, which works for any
`DyninMityaginSpace E` without needing Polish/Borel instances.

## Statements

- `configuration_torus_polish`: `PolishSpace (Configuration (TorusTestFunction L))`
- `configuration_torus_borelSpace`: cylindrical σ-algebra = Borel σ-algebra

## Proof strategies

### Strategy A: Closed embedding into ℕ → ℝ

Show `configBasisEval : Configuration E → (ℕ → ℝ)` is a closed embedding
for any `DyninMityaginSpace E`. Then:
- `PolishSpace` via `IsClosedEmbedding.polishSpace` (ℕ → ℝ is Polish)
- `BorelSpace` via `MeasurableEmbedding.borelSpace` + `borel_comap`

Key steps:
1. **Embedding**: Show the weak-* topology equals the initial topology of
   `configBasisEval`. Requires: if `ω_n(basis_m) → ω(basis_m)` for all m,
   then `ω_n(e) → ω(e)` for all e. The DM expansion gives
   `ω(e) = Σ_m coeff_m(e) · ω(basis_m)` with rapid decay of `coeff_m(e)`.
   Interchange of limit and sum needs equicontinuity of `{ω_n}`, which
   follows from Banach-Steinhaus for Fréchet spaces (pointwise bounded ⟹
   equicontinuous on barrelled spaces).
   Mathlib has `WithSeminorms.banach_steinhaus` — needs verification that
   it provides the right form.

2. **Closed image**: The image consists of polynomial-growth sequences
   (CLFs on DM spaces have polynomially-bounded basis evaluations).
   A pointwise limit of such sequences that are equicontinuous (by
   Banach-Steinhaus) remains a CLF, so the image is sequentially closed,
   hence closed (since ℕ → ℝ is first-countable).

3. **BorelSpace**: Once `configBasisEval` is an embedding,
   `instMeasurableSpaceConfiguration_eq_comap` + `borel_comap` gives
   `instMeasurableSpaceConfiguration = borel (Configuration E)`.

Estimated difficulty: ~300-500 LOC if `WithSeminorms.banach_steinhaus`
fits; much more if not.

This strategy would generalize beyond `TorusTestFunction` to all
`DyninMityaginSpace E`.

### Strategy B: Nuclear Fréchet dual theory (traditional)

The weak-* dual of a nuclear Fréchet space is Polish. Standard references:
- Schaefer, *Topological Vector Spaces* Ch. III §7, IV §9
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 Ch. IV

Key steps:
1. Nuclear Fréchet ⟹ Montel (bounded sets are relatively compact)
2. Montel ⟹ semi-reflexive
3. Metrizability of weak-* on duals of nuclear Fréchet spaces
4. Completeness via Banach-Steinhaus for Fréchet spaces
5. Second-countability from σ-compactness + metrizability
6. BorelSpace: second-countable ⟹ cylindrical σ-algebra = Borel

None of the nuclear-specific steps (Montel, semi-reflexive, metrizability
of weak-* dual) are in Mathlib as of early 2026.

Estimated difficulty: 800-1500 LOC of nuclear space infrastructure.

## References

- Schaefer, *Topological Vector Spaces* Ch. III §7, IV §9
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 Ch. IV
- Bogachev, *Gaussian Measures* Ch. 2-3
-/

-- This file is intentionally not imported by any active module.
-- It serves as documentation for future proof targets.
