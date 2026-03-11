# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, and the FKG inequality for use by downstream
projects (pphi2, OSforGFF).

**0 axioms (+1 skipped), 0 sorries**

*Updated 2026-03-10.*

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

Former axiom `mehlerKernel_eq_series` (Mehler's formula) has been moved to
`future/mehler_kernel.lean` (not counted as project axiom). `HeatKernel/PositionKernel.lean`
is off the main build path — it contains 2000+ lines of proved cylinder QFT results
that depend on this axiom, but none are used by pphi2.

Proved heat kernel results (no longer axioms):
- `circleHeatKernel_pos` -- **proved** (via `HurwitzZeta.cosKernel` + Poisson summation / functional equation). The circleHeatKernel eigenvalue bug (index vs frequency mismatch) was fixed: now uses `fourierFreq n` for the Laplacian eigenvalue.
- `cylinderEval_summable` -- theorem
- `integral_norm_tsum_le_tsum_integral_norm` -- theorem
- `integrable_tsum_of_summable_integral_norm` -- theorem

Proved heat kernel bilinear form results:
- `heatKernelBilinear_summable` — summability of heat kernel series for t > 0
- `heatKernelBilinear_nonneg` — K_t(f,f) ≥ 0
- `heatKernelBilinear_le_l2` — K_t(f,f) ≤ ⟨f,f⟩_{L²} (proved)
- `heatKernelBilinear_tendsto_l2` — K_t → L² as t → 0⁺ (dominated convergence, proved)
- `greenFunctionBilinear_summable` — summability of Green's function series (proved)
- `greenFunctionBilinear_nonneg` — G(f,f) ≥ 0
- `greenFunctionBilinear_le` — G(f,f) ≤ (1/mass²)⟨f,f⟩ (proved)
- `greenFunctionBilinear_pos` — G(f,f) > 0 for f ≠ 0 (proved via Hahn-Banach)

Remaining sorry:
- `heatKernelBilinear_tensorProduct`: K_t factors under ⊗. Requires Fubini for tsum + coefficient factorization.

### Torus embedding (continuum limit infrastructure)

Proved torus results:
- `evalCLM` -- **proved** (tensor product of continuous linear functionals via `lift` + `Seminorm.bound_of_continuous`)
- `evalCLM_pure` -- **proved** (via `lift_pure`)
- `circleRestriction` -- CLM sampling smooth periodic functions at lattice points
- `evalTorusAtSite` -- evaluation of torus test function at lattice site
- `torusEmbedCLM` -- embedding of lattice fields into Configuration space

Former axioms `configuration_torus_polish` and `configuration_torus_borelSpace` have been
moved to `future/configuration_torus.lean` (not counted as project axioms). Their intended
use (Prokhorov's theorem) is now handled by `prokhorov_configuration` in
`GaussianField/ConfigurationEmbedding.lean`, which works for any `DyninMityaginSpace E`
without needing Polish/Borel instances on Configuration.

### Support theorem

Former axioms `not_supported_of_not_hilbertSchmidt` and `supportHilbertSpace_exists`
have been moved to `future/gaussian_field_axioms.lean` (not counted as project axioms).
Neither is used by pphi2 or any downstream code.

Proved support results:
- `expected_norm_sq_eq_hs` — theorem: E[Σₙ|ω(eₙ)|²] = Σₙ ‖T(eₙ)‖² via integral_tsum
- `support_of_hilbertSchmidt` — theorem: HS ⟹ a.e. summable (forward direction via ae_lt_top)
- `weighted_support` — theorem: weighted-HS ⟹ a.e. weighted-summable (generalized forward direction)

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

### Lattice convergence (1D heat kernel)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| ~~`latticeHeatKernelBilinear1d_eq_spectral`~~ | Lattice/CirculantDFT | **PROVED** | Hard | Corrected DFT spectral expansion with /normSq Nyquist fix (`latticeHeatKernelBilinear1d_eq_spectral'`). |
| ~~`riemann_sum_periodic_tendsto`~~ | Lattice/HeatKernelConvergence1d | **PROVED** | | Riemann sum convergence for continuous periodic functions via uniform continuity + subinterval splitting. |
| ~~`latticeDFTCoeff1d_uniform_bound`~~ | Lattice/HeatKernelConvergence1d | **PROVED** | | Replaced by flat bound `|c_m| <= sqrt(2L) * ||f||_C0` + eigenvalue lower bound via Jordan's inequality. Convergence uses `exp(-8tm/L^2)` geometric domination instead of `1/(1+m)^2` polynomial decay. |

Proved lattice convergence results:
- `latticeEigenvalue1d_tendsto` -- eigenvalue convergence via sinc (proved)
- `latticeEigenvalue1d_tendsto_continuum` -- eigenvalue convergence for general modes (proved)
- `restriction_times_latticeBasis` -- normalization identity (proved)
- `riemann_sum_periodic_tendsto` -- Riemann sum convergence for periodic functions (proved)
- `latticeDFTCoeff1d_tendsto` -- DFT coefficient convergence via Riemann sums (proved)
- `latticeDFTCoeff1d_flat_bound` -- uniform bound on DFT coefficients (proved)
- `latticeEigenvalue1d_ge_8m` -- eigenvalue lower bound via Jordan's inequality (proved)
- `latticeDFTCoeff1d_eq_riemann_sum` -- DFT coefficient equals Riemann sum of f times fourierBasisFun (proved)
- `latticeDFTCoeff1d_tendsto` -- **proved** (was axiom): DFT coefficient converges to continuum Fourier coefficient via Riemann sum convergence
- `lattice_heatKernel_tendsto_continuum_1d` -- full 1D heat kernel bilinear form convergence (proved, uses Tannery's theorem / dominated convergence for sums)

### Lattice convergence (Green's function)

| Item | File | Type | Difficulty | Description |
|------|------|------|-----------|-------------|
| ~~`lattice_covariance_pure_eq_2d_spectral`~~ | Lattice/Convergence | **proved** | Medium | Circulant diagonalization via `abstract_spectral_eq_dft_spectral_2d` + pure tensor factoring + `evalCLM_pure`. |
| ~~`latticeDFTCoeff1d_quadratic_bound`~~ | Lattice/Convergence | **proved** | — | Eliminated: replaced by flat bound + eigenvalue lower bound via Jordan's inequality. |
| `lattice_green_tendsto_continuum_pure` | Lattice/Convergence | **proved** | — | Convergence for pure tensors via Tannery's theorem on ℕ×ℕ. |
| ~~`lattice_green_tendsto_continuum`~~ | Lattice/Convergence | **proved** | — | Bilinear extension from pure tensors to general elements via DM expansion + uniform polynomial bound. |

### Green's function invariance

Proved Green's function invariance results (no longer axioms):
- `greenFunctionBilinear_reflection_pure` -- **proved** (mode-partner involution with eigenvalue degeneracy)
- `greenFunctionBilinear_translation_pure` -- **proved** (coeff_product_paired_translation + tsum_eq_of_paired_involution)
- `greenFunctionBilinear_invariant_of_pure` -- **proved** (two-step DyninMityaginSpace expansion via greenCLM_left)

### Gaussian field uniqueness

Former axiom `measure_unique_of_charFun` has been moved to
`future/gaussian_field_axioms.lean` (not counted as project axiom).
Not currently used by any downstream code.

### Fourier translation/reflection

Proved Fourier results (no longer axioms):
- `fourierCoeffReal_circleTranslation_zero` -- **proved** (periodicity of integration via `integral_Icc_comp_sub_of_periodic`)
- `fourierCoeffReal_circleTranslation_cos` -- **proved** (cos addition formula + integral linearity + periodicity)
- `fourierCoeffReal_circleTranslation_sin` -- **proved** (sin addition formula + integral linearity + periodicity)
- `fourierCoeffReal_circleReflection_zero` -- **proved** (periodicity of integration via `integral_Icc_comp_neg_of_periodic`)
- `fourierCoeffReal_circleReflection_cos` -- **proved** (cosine is even: `fourierBasisFun_even_cos`)
- `fourierCoeffReal_circleReflection_sin` -- **proved** (sine is odd: `fourierBasisFun_odd_sin`)

### Nuclear tensor product functors

Proved nuclear tensor product results (no longer axioms):
- `nuclearTensorProduct_mapCLM` -- **proved** (tensor product of CLMs via Schauder basis coefficient mapping + polynomial growth/decay bounds)
- `nuclearTensorProduct_mapCLM_pure` -- **proved** (DM expansion + `tsum_mul_tsum_of_summable_norm` + Cantor pairing reindex)
- `nuclearTensorProduct_mapCLM_id` -- **proved** (biorthogonality collapses sum via `tsum_eq_single`)
- `nuclearTensorProduct_mapCLM_comp` -- **proved** (DM expansion on basis vectors + `mapCLM_pure` for agreement)
- `nuclearTensorProduct_swapCLM` -- **proved** (Cantor pair permutation `m ↦ pair(unpair(m).2, unpair(m).1)`, rapid decay via `1+m ≤ 4·(1+σ(m))²`)
- `nuclearTensorProduct_swapCLM_pure` -- **proved** (commutativity of multiplication on coefficients)

### Summary by file

| File | Axioms | Sorries |
|------|--------|---------|
| GaussianField/Properties | 0 | 0 |
| GaussianField/Support | 0 | 0 |
| Lattice/Convergence | 0 | 0 |
| Torus/Restriction | 0 | 0 |
| Nuclear/TensorProductFunctorAxioms | 0 | 0 |
| **Total** | **0 (+1 skipped)** | **0** |

## References

- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) -- FKG inequality
- Gelfand-Vilenkin, *Generalized Functions Vol. 4* -- nuclear spaces
- Bogachev, *Gaussian Measures* -- Gaussian measures on Frechet spaces
