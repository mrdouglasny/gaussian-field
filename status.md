# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, and the FKG inequality for use by downstream
projects (pphi2, OSforGFF-dimensions).

**16 axioms, 12 sorries**

*Updated 2026-02-24.*

## Axiom inventory

### Used by pphi2 Normalization (FKG)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `fkg_from_lattice_condition` | Lattice/FKG | axiom | Hard | Core FKG: lattice condition => correlation inequality (Holley 1974). |
| `integrable_mul_gaussianDensity` | Lattice/FKG | axiom | Medium | Integrability of f*gaussianDensity (fixed: added integrability hypothesis). |
| `latticeGaussianMeasure_density_integral` | Lattice/FKG | axiom | Medium | Gaussian measure density integral formula. |

Proved FKG results (no longer axioms):
- `gaussian_fkg_lattice_condition` -- now a theorem
- `fkg_perturbed` -- now a theorem
- `fkg_lattice_gaussian` -- derived from `gaussian_fkg_lattice_condition`

### Infinite lattice (not needed by pphi2)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `latticeEnum_norm_bound` | Lattice/RapidDecayLattice | axiom | Hard | ‖enum^{-1}(m)‖ <= C*m^{1/d}. |
| `latticeEnum_index_bound` | Lattice/RapidDecayLattice | axiom | Hard | enum(x) <= C*(1+‖x‖)^d. |
| `latticeRapidDecayEquiv` | Lattice/RapidDecayLattice | axiom | Hard | CLE to RapidDecaySeq. |

### Heat kernel (cylinder QFT, not used by lattice approach)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `mehlerKernel_eq_series` | HeatKernel/PositionKernel | axiom | Hard | Mehler's formula. |
| `circleHeatKernel_pos` | HeatKernel/PositionKernel | axiom | Hard | Requires Poisson summation. |
| `cylinderEval_summable` | HeatKernel/PositionKernel | axiom | Medium | Convergence of eigenfunction expansion. |

### Hypercontractive estimates

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| `gaussian_hypercontractive` | GaussianField/Hypercontractive | axiom | Hard | Nelson's hypercontractive estimate: ‖ω(f)^n‖_{Lᵖ} ≤ (p-1)^{n/2} · ‖ω(f)^n‖_{L²}. |

Proved hypercontractive results:
- `gross_log_sobolev` -- now a theorem (1D reduction via `pairing_is_gaussian` + `log(y) ≤ y-1`)

### Infrastructure

| Item | File | Type | Description |
|------|------|------|-------------|
| `schwartz_dyninMityaginSpace_axiom` | GaussianField | axiom | Schwartz space is a Dynin-Mityagin space (nuclear Frechet). |

### Summary by file

| File | Axioms | Sorries |
|------|--------|---------|
| HeatKernel/PositionKernel | 3 | 2 |
| Lattice/RapidDecayLattice | 3 | 1 |
| Lattice/FKG | 9 | 0 |
| Lattice/SpectralCovariance | 0 | 7 |
| GaussianField/Density | 0 | 2 |
| GaussianField/Hypercontractive | 1 | 0 |
| **Total** | **16** | **12** |

## References

- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) -- FKG inequality
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* -- nuclear spaces
- Bogachev, *Gaussian Measures* -- Gaussian measures on Frechet spaces
