# gaussian-field TODO

## Infrastructure to eliminate axioms

### 1. DFT / circulant diagonalization on Z/NZ (eliminates ~3 axioms)

Target axioms:
- `latticeHeatKernelBilinear1d_eq_spectral` (Lattice/HeatKernelConvergence1d)
- `lattice_covariance_pure_eq_2d_spectral` (Lattice/Convergence)
- ~~`latticeDFTCoeff1d_quadratic_bound` (Lattice/Convergence)~~ — **DONE** (Lattice/CirculantDFT.lean)

What to build:
- DFT on Z/NZ as a unitary map (Mathlib has `dft` but not circulant theory)
- Circulant matrices diagonalized by DFT
- Eigenvalue formula: lambda_k = (4/a^2) sum_i sin^2(pi k_i / N)
- Summation by parts on Z/NZ for quadratic coefficient decay

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
