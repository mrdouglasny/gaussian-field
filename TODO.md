# gaussian-field TODO

## Infrastructure to eliminate axioms

### 1. DFT / circulant diagonalization on Z/NZ (eliminates ~3 axioms)

Target axioms:
- `latticeHeatKernelBilinear1d_eq_spectral` (Lattice/HeatKernelConvergence1d)
- `lattice_covariance_pure_eq_2d_spectral` (Lattice/Convergence)
- `latticeDFTCoeff1d_quadratic_bound` (Lattice/Convergence) — via summation by parts

What to build:
- DFT on Z/NZ as a unitary map (Mathlib has `dft` but not circulant theory)
- Circulant matrices diagonalized by DFT
- Eigenvalue formula: lambda_k = (4/a^2) sum_i sin^2(pi k_i / N)
- Summation by parts on Z/NZ for quadratic coefficient decay

### 2. Green's function invariance on pure tensors (eliminates 2 axioms)

Target axioms:
- `greenFunctionBilinear_reflection_pure` (HeatKernel/GreenInvariance)
- `greenFunctionBilinear_translation_pure` (HeatKernel/GreenInvariance)

Now provable: the Fourier coefficient transformation theorems in
`SmoothCircle/FourierTranslation.lean` are all proved. The proofs need:
- `pure_val` (coefficient factorization for pure tensors)
- Term-by-term invariance for reflection (sign cancellation: (+-1)^2 = 1)
- Paired-mode regrouping for translation (`paired_coeff_product_circleTranslation`)

### 3. Bilinear extension from pure tensors (eliminates 2 axioms)

Target axioms:
- `greenFunctionBilinear_invariant_of_pure` (HeatKernel/GreenInvariance)
- `lattice_green_tendsto_continuum` (Lattice/Convergence)

General principle: if a continuous bilinear identity holds on
`NuclearTensorProduct.pure`, it holds on all elements (by density of
pure tensors + continuity of the bilinear form).

What to build:
- Density of `pure` elements in `NuclearTensorProduct`
- Extension lemma: continuous bilinear identity on dense subset extends

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
