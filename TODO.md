# gaussian-field TODO

## Infrastructure to eliminate axioms

### 1. DFT / circulant diagonalization on Z/NZ (eliminates ~3 axioms)

Target axioms:
- ~~`latticeHeatKernelBilinear1d_eq_spectral` (Lattice/HeatKernelConvergence1d)~~ — **DONE** (Lattice/CirculantDFT.lean)
- `lattice_covariance_pure_eq_2d_spectral` (Lattice/Convergence)
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
- `lattice_covariance_pure_eq_2d_spectral`: 2D version of spectral expansion

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

### 5. Nuclear tensor product functor (eliminates 6 axioms)

Target axioms (all in Nuclear/TensorProductFunctorAxioms):
- `nuclearTensorProduct_mapCLM`
- `nuclearTensorProduct_swapCLM`
- `nuclearTensorProduct_mapCLM_comp`
- `nuclearTensorProduct_mapCLM_id`
- `nuclearTensorProduct_mapCLM_pure`
- `nuclearTensorProduct_swapCLM_pure`

Construction: CLMs on DyninMityaginSpaces have polynomial growth on basis
coefficients (by coeff_decay + basis_growth). On the Kothe sequence space
representation, T1 ot T2 acts coefficient-wise via Cantor pairing.
Swap is the Cantor pairing transpose. ~500+ LOC.
