# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, and the FKG inequality for use by downstream
projects (pphi2, OSforGFF-dimensions).

**5 axioms, 0 sorries**

*Updated 2026-02-26.*

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
| `latticeEnum_norm_bound` | Lattice/RapidDecayLattice | axiom | Hard | ‖enum^{-1}(m)‖ <= C*m^{1/d}. (requires `d ≥ 1`) |
| `latticeEnum_index_bound` | Lattice/RapidDecayLattice | axiom | Hard | enum(x) <= C*(1+‖x‖)^d. (requires `d ≥ 1`) |
| `latticeRapidDecayEquiv` | Lattice/RapidDecayLattice | axiom | Hard | CLE to RapidDecaySeq (enumeration branch excludes `d=0`). |

### Heat kernel (cylinder QFT, not used by lattice approach)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `mehlerKernel_eq_series` | HeatKernel/PositionKernel | axiom | Hard | Mehler's formula. |
| `circleHeatKernel_pos` | HeatKernel/PositionKernel | axiom | Hard | Requires Poisson summation. |
| `cylinderEval_summable` | HeatKernel/PositionKernel | theorem | Medium | Convergence of eigenfunction expansion. |
| `integral_norm_tsum_le_tsum_integral_norm` | HeatKernel/PositionKernel | theorem | Medium | Dominated-convergence corollary: integral norm of series ≤ series of integral norms. |
| `integrable_tsum_of_summable_integral_norm` | HeatKernel/PositionKernel | theorem | Medium | Dominated-convergence corollary: summable integral norms imply integrable pointwise tsum. |

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
| HeatKernel/PositionKernel | 2 | 0 |
| Lattice/RapidDecayLattice | 3 | 0 |
| Lattice/FKG | 0 | 0 |
| Lattice/SpectralCovariance | 0 | 0 |
| GaussianField/Density | 0 | 0 |
| GaussianField/Hypercontractive | 0 | 0 |
| **Total** | **5** | **0** |

## References

- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) -- FKG inequality
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* -- nuclear spaces
- Bogachev, *Gaussian Measures* -- Gaussian measures on Frechet spaces
