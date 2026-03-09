# gaussian-field TODO

## Infrastructure to eliminate axioms

### 1. DFT / circulant diagonalization on Z/NZ (eliminates ~3 axioms)

Target axioms:
- ~~`latticeHeatKernelBilinear1d_eq_spectral` (Lattice/HeatKernelConvergence1d)~~ — **DONE** (Lattice/CirculantDFT.lean)
- ~~`lattice_covariance_pure_eq_2d_spectral` (Lattice/Convergence)~~ — **DONE** (Lattice/CirculantDFT2d.lean)
- ~~`latticeDFTCoeff1d_quadratic_bound` (Lattice/Convergence)~~ — **DONE** (Lattice/CirculantDFT.lean)

Progress:
- **DONE** (Lattice/HeatKernel.lean): `bilinear_exp_eq_spectral` — spectral expansion
  of the matrix exponential bilinear form using Mathlib's abstract eigenbasis.
  Also `mulVec_exp_neg_smul` and `eigenCoeff_exp_neg_smul`.
- **DONE** (Lattice/CirculantDFT.lean): eigenvector theorems
  `negLaplacian1d_cos_eigenvalue`, `negLaplacian1d_sin_eigenvalue`
- **DONE** (Lattice/CirculantDFT.lean): corrected spectral expansion
  `latticeHeatKernelBilinear1d_eq_spectral'` — includes `/latticeFourierNormSq`
  correction for Nyquist mode normalization. Required: DFT basis construction
  (`latticeFourierBasis`), DFT expansion (`dft_expansion`), eigenvector property
  (`negLaplacian1d_dft_eigenvector`), matrix exponential eigenvector theorem.
  Also proved `latticeFourierNormSq_nyquist`, `latticeFourierNormSq_ge_one`,
  `latticeFourierNormSq_eventually_one` for convergence.

What remains:
- ~~`lattice_covariance_pure_eq_2d_spectral`: 2D version of spectral expansion~~ — **DONE**
  Proved via `abstract_spectral_eq_dft_spectral_2d` (2D DFT Parseval + product eigenvectors
  + mass operator surjectivity) + pure tensor factoring via `evalCLM_pure`.

### 2. Green's function invariance on pure tensors (eliminates 2 axioms)

Target axioms:
- ~~`greenFunctionBilinear_reflection_pure` (HeatKernel/GreenInvariance)~~ — **DONE**
- ~~`greenFunctionBilinear_translation_pure` (HeatKernel/GreenInvariance)~~ — **DONE**

Proved using `pure_val`, `fourierCoeffReal_reflection_product`,
`coeff_product_paired_translation`, and `tsum_eq_of_paired_involution`
(mode-partner involution with eigenvalue degeneracy).

### 3. Bilinear extension from pure tensors (eliminates 2 axioms)

Target axioms:
- ~~`greenFunctionBilinear_invariant_of_pure` (HeatKernel/GreenInvariance)~~ — **DONE**
- `lattice_green_tendsto_continuum` (Lattice/Convergence)

Proved `invariant_of_pure` via two-step DyninMityaginSpace expansion:
fix a pure tensor in arg 2, expand arg 1 using CLM `greenCLM_left`;
then fix arg 1, expand arg 2 the same way. Requires biorthogonality
`coeff n (basis m) = δ_{nm}` (holds for `ofRapidDecayEquiv` instances).

### 4. Measure uniqueness from characteristic function (eliminates 1+ axioms)

Target axioms:
- `measure_unique_of_charFun` (GaussianField/Properties)

Levy's uniqueness theorem: if two finite Borel measures on a nuclear
Frechet dual have the same characteristic functional, they are equal.
Standard reference: Gel'fand-Vilenkin Vol. 4.

### 5. Nuclear tensor product functor — **DONE** (all 4 axioms eliminated)

All target axioms proved (Nuclear/TensorProductFunctorAxioms):
- **DONE**: `nuclearTensorProduct_mapCLM` — definition + continuity proof
- **DONE**: `nuclearTensorProduct_mapCLM_pure` — DM expansion + norm-summable product
- **DONE**: `nuclearTensorProduct_mapCLM_id` — biorthogonality sum collapse
- **DONE**: `nuclearTensorProduct_mapCLM_comp` — DM expansion on basis vectors + `mapCLM_pure`
- **DONE**: `nuclearTensorProduct_swapCLM` — Cantor pair permutation
- **DONE**: `nuclearTensorProduct_swapCLM_pure` — commutativity of multiplication
