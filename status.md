# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, and the FKG inequality for use by downstream
projects (pphi2, OSforGFF-dimensions).

**17 axioms, 0 sorries**

*Updated 2026-02-25.*

## Axiom inventory

### Used by pphi2 Normalization (FKG)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `fkg_from_lattice_condition` | Lattice/FKG | theorem | Hard | Core FKG: lattice condition => correlation inequality (Holley 1974). |
| `integrable_mul_gaussianDensity` | GaussianField/Density | axiom | Medium | Integrability transfer from Gaussian measure to weighted Lebesgue integral. |
| `latticeGaussianMeasure_density_integral` | GaussianField/Density | axiom | Medium | Gaussian measure density integral formula. |

Proved FKG results (no longer axioms):
- `gaussian_fkg_lattice_condition` -- now a theorem
- `fkg_perturbed` -- now a theorem
- `fkg_lattice_gaussian` -- derived from `gaussian_fkg_lattice_condition`

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
| `cylinderEval_summable` | HeatKernel/PositionKernel | axiom | Medium | Convergence of eigenfunction expansion. |
| `integral_norm_tsum_le_tsum_integral_norm` | HeatKernel/PositionKernel | axiom | Medium | Dominated-convergence corollary: integral norm of series ≤ series of integral norms. |
| `integrable_tsum_of_summable_integral_norm` | HeatKernel/PositionKernel | axiom | Medium | Dominated-convergence corollary: summable integral norms imply integrable pointwise tsum. |

### Hypercontractive estimates

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `gaussian_moment_ratio_bound` | GaussianField/Hypercontractive | axiom | Hard | Core Gamma-function inequality used in 1D hypercontractivity. |

Proved hypercontractive results (derived using the axiom above):
- `gaussian_hypercontractive` -- theorem
- `gross_log_sobolev` -- theorem

### Infrastructure

| Item | File | Type | Description |
|------|------|------|-------------|
| `schwartz_dyninMityaginSpace_axiom` | GaussianField | axiom | Schwartz space is a Dynin-Mityagin space (nuclear Frechet). |

### Summary by file

| File | Axioms | Sorries |
|------|--------|---------|
| HeatKernel/PositionKernel | 5 | 0 |
| Lattice/RapidDecayLattice | 3 | 0 |
| Lattice/FKG | 5 | 0 |
| Lattice/SpectralCovariance | 0 | 0 |
| GaussianField/Density | 2 | 0 |
| GaussianField/Hypercontractive | 1 | 0 |
| GaussianField | 1 | 0 |
| **Total** | **17** | **0** |

## References

- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) -- FKG inequality
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* -- nuclear spaces
- Bogachev, *Gaussian Measures* -- Gaussian measures on Frechet spaces
