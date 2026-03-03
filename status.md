# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, and the FKG inequality for use by downstream
projects (pphi2, OSforGFF).

**4 axioms, 0 sorries**

*Updated 2026-03-03.*

## Axiom inventory

### Used by pphi2 Normalization (FKG)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `fkg_from_lattice_condition` | Lattice/FKG | theorem | Hard | Core FKG: lattice condition => correlation inequality (Holley 1974). |
| `latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure` | GaussianField/Density | theorem | Hard | Master density theorem: field-law pushforward equals normalized density measure. |

Density rewrite progress (P0 master theorem path):
- Added `evalMap` measurability and `latticeGaussianFieldLaw` wrapper in
  `GaussianField/Density.lean`.
- Added transport lemmas between `latticeGaussianFieldLaw` and composition with
  `evalMap` (`Integrable.comp_evalMap_latticeGaussianFieldLaw`,
  `Integrable.of_comp_evalMap_latticeGaussianFieldLaw`,
  `integral_latticeGaussianFieldLaw`).
- Added normalization scaffolding for density measure:
  `gaussianDensityWeight_measurable`, `gaussianDensityNormConst_eq_lintegral`,
  `gaussianDensityNormConst_ne_top`, `gaussianDensityNormConst_eq_ofReal_integral`.
- Replaced density axioms `latticeGaussianMeasure_density_integral` and
  `integrable_mul_gaussianDensity` with theorem proofs derived from the proved
  master density law. The old names remain as theorems for compatibility.

Proved FKG results (no longer axioms):
- `ahlswede_daykin_ennreal` -- theorem (ENNReal n-dimensional induction)
- `ahlswede_daykin` -- theorem (Real wrapper via ENNReal bridge)
- `gaussian_fkg_lattice_condition` -- now a theorem
- `fkg_perturbed` -- now a theorem
- `fkg_lattice_gaussian` -- derived from `gaussian_fkg_lattice_condition`
- `fkg_truncation_dct` -- now a theorem
- `fkg_truncation_dct_prod` -- now a theorem
- `integrable_truncation_mul` -- now a theorem
- `integrable_truncation_prod_mul` -- now a theorem
- `ad_marginal_preservation_ennreal` -- theorem (fiber-to-marginal AD in ENNReal)
- removed axiomized AD transport path from `Lattice/FKG`

### Infinite lattice (not needed by pphi2)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `latticeEnum_norm_bound` | Lattice/RapidDecayLattice | theorem | Hard | Polynomial inverse bound: ‖enum^{-1}(m)‖ <= C*(1+m)^p (proved by induction on pairing depth). |
| `latticeEnum_index_bound` | Lattice/RapidDecayLattice | theorem | Hard | Polynomial forward bound: enum(x) <= C*(1+‖x‖)^q (proved by induction on pairing depth). |
| `latticeRapidDecayEquiv` | Lattice/RapidDecayLattice | theorem | Hard | CLE to RapidDecaySeq (proved using polynomial reindexing bounds; enumeration branch excludes `d=0`). |

### Heat kernel (cylinder QFT, not used by lattice approach)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `mehlerKernel_eq_series` | HeatKernel/PositionKernel | axiom | Hard | Mehler's formula. |

Proved heat kernel results (no longer axioms):
- `circleHeatKernel_pos` -- **proved** (via `HurwitzZeta.cosKernel` + Poisson summation / functional equation). The circleHeatKernel eigenvalue bug (index vs frequency mismatch) was fixed: now uses `fourierFreq n` for the Laplacian eigenvalue.
- `cylinderEval_summable` -- theorem
- `integral_norm_tsum_le_tsum_integral_norm` -- theorem
- `integrable_tsum_of_summable_integral_norm` -- theorem

Remaining axiom:
- `mehlerKernel_eq_series`: Mehler's formula (Hermite eigenfunction expansion of harmonic oscillator heat kernel). Requires Hermite polynomial generating function, not in Mathlib.

### Torus embedding (continuum limit infrastructure)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `configuration_torus_polish` | Torus/Restriction | axiom | Hard | PolishSpace for weak-* dual of nuclear Fréchet space. |
| `configuration_torus_borelSpace` | Torus/Restriction | axiom | Moderate | Cylindrical σ-algebra = Borel σ-algebra for nuclear Fréchet dual. |

Proved torus results:
- `evalCLM` -- **proved** (tensor product of continuous linear functionals via `lift` + `Seminorm.bound_of_continuous`)
- `evalCLM_pure` -- **proved** (via `lift_pure`)
- `circleRestriction` -- CLM sampling smooth periodic functions at lattice points
- `evalTorusAtSite` -- evaluation of torus test function at lattice site
- `torusEmbedCLM` -- embedding of lattice fields into Configuration space

Elimination analysis for Polish/Borel axioms:
- The naive approach (reformulate as `ℕ → ℝ` via Fourier coefficients) does NOT work:
  the dual of `RapidDecaySeq` is the space of polynomial-growth sequences, which is
  F_σ (not closed) in `ℕ → ℝ` and is NOT Polish with the subspace topology (it is
  meager in itself, violating Baire's theorem for completely metrizable spaces).
- The weak-* topology on s' IS Polish (standard result: Gel'fand-Vilenkin Vol. 4,
  Schaefer III§7/IV§9), but proving this requires nuclear Fréchet space theory not
  in Mathlib: metrizability of weak-* dual via Montel property + nuclear compactness,
  Banach-Steinhaus for Fréchet spaces (`WithSeminorms.banach_steinhaus` exists but
  the nuclear-specific ingredients do not). Estimated effort: 500-1000+ LOC.
- BorelSpace (cylindrical = Borel) requires second-countability of the weak-* topology,
  which is part of the same nuclear space theory.
- **Decision**: keep as axioms. Used in pphi2 `TorusContinuumLimit/` for Prokhorov's
  theorem. The mathematical justification is solid; the Lean infrastructure gap is
  in Mathlib's nuclear space library, not in our project.

### Hypercontractive estimates

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `gaussian_moment_ratio_bound` | *(removed)* | ~~axiom~~ | Hard | **Eliminated**: proved via double-factorial combinatorics in `HypercontractiveNat.lean`. |

Proved hypercontractive results (axiom-free):
- `hypercontractive_1d_even` -- theorem (direct combinatorial proof for even p)
- `hypercontractive_1d` -- theorem (rpow wrapper, even p)
- `hypercontractive_gaussianReal` -- theorem (variance scaling)
- `gaussian_hypercontractive` -- theorem (infinite-dimensional pushforward)
- `gross_log_sobolev` -- theorem (independent of the above chain)

### Infrastructure (inactive, for testing only)

| Item | File | Type | Description |
|------|------|------|-------------|
| `schwartz_dyninMityaginSpace_axiom` | GaussianField | commented out | Axiom fallback for Schwartz ≅ Dynin-Mityagin space; the proven instance via `SchwartzNuclear.HermiteTensorProduct` is used instead. Available to swap in for faster build/testing. |

### Summary by file

| File | Axioms | Sorries |
|------|--------|---------|
| HeatKernel/PositionKernel | 1 | 0 |
| Torus/Restriction | 2 | 0 |
| Lattice/RapidDecayLattice | 0 | 0 |
| Lattice/FKG | 0 | 0 |
| Lattice/SpectralCovariance | 0 | 0 |
| GaussianField/Density | 0 | 0 |
| GaussianField/Hypercontractive | 0 | 0 |
| Nuclear/NuclearTensorProduct | 0 | 0 |
| **Total** | **3 (+1 skipped)** | **0** |

## References

- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) -- FKG inequality
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* -- nuclear spaces
- Bogachev, *Gaussian Measures* -- Gaussian measures on Frechet spaces
