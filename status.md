# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, the FKG inequality, and cylinder QFT
infrastructure for use by downstream projects (pphi2, OSforGFF).

**4 axioms, 0 sorries** (active build, excluding `future/`)

*Updated 2026-04-14.*

### Recent additions

- **Lattice/CombesThomas.lean** (760 lines, fully proved): Combes-Thomas
  exponential decay estimate for resolvent entries of finite-range PD
  matrices. `|M⁻¹(x,y)| ≤ C · exp(-α · dist(x,y))`. Used by pphi2N
  for the mass gap Green's function decay bound.

## Active Axiom Inventory (4 axioms)

### Cylinder Green's function (2 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 1 | `resolventSchwartz_uniformBound` | SchwartzFourier/ResolventUniformBound | Resolvent Schwartz seminorm bounds uniform in $\omega \geq m$. Proof route: factorization $R_\omega = R_m \circ M_{\tau_\omega}$ with proved identity $\sigma_m \cdot \tau_\omega = \sigma_\omega$. (Relocated from Cylinder/MassOperatorConstruction.) |
| 2 | `cylinderMassOperator_equivariant_of_heat_comm` | Cylinder/GreenFunction | Heat kernel equivariance principle: if CLM $S$ commutes with $e^{-tA}$ for all $t \geq 0$, then $T$ intertwines $S$ with an isometry $U$ on $\ell^2$. |

Note: `cylinderMassOperator` is now a **definition** (constructed from `ntpSliceSchwartz` + `resolventMultiplierCLM` + `nuclear_ell2_embedding_from_decay`). `cylinderGreen_pos` is a **proved theorem** from `cylinderMassOperator_injective`. `cylinderGreen_continuous_seminorm_bound` is a **proved theorem**.

### Cylinder reflection positivity (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 3 | `cylinderGreen_reflection_eq_laplaceNorm` | Cylinder/ReflectionPositivity | Laplace factorization: $G(f, \Theta f) = \lVert \Lambda f \rVert^2$ for positive-time $f$. Resolvent kernel factors as $e^{-\omega t} \cdot e^{\omega s} / (2\omega)$ for $t > 0 > s$. |

Note: `cylinderGreen_reflection_positive` ($G(f,\Theta f) \geq 0$) is a **proved theorem** from the Laplace factorization identity. `cylinderGreen_reflection_strict_positive` was removed as a dead axiom.

### Method of images (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 4 | `embed_l2_uniform_bound` | Cylinder/MethodOfImages | $\lVert \text{embed}\,f \rVert_{\ell^2}^2 \leq q(f)^2$ uniformly in $L_t \geq 1$. Uniform ℓ² bound for the periodization embedding. |

Note: `torusGreen_uniform_bound` is a **proved theorem** from `embed_l2_uniform_bound` + `greenFunctionBilinear_le`. `cylinderToTorusEmbed` is a **definition** (not axiom).

## Inactive / Future Axioms (not counted)

| Name | File | Description |
|------|------|-------------|
| `schwartz_dyninMityaginSpace_axiom` | GaussianField.lean | Fallback axiom (commented out). Proved instance used instead. |
| `NuclearSpaceStd` | future/KolmogorovGaussian | Alternative Gaussian construction via Cipollina's framework |
| `kolmogorov_gaussian_measure` | future/KolmogorovGaussian | Kolmogorov-Minlos existence |
| `mehlerKernel_eq_series` | future/PositionKernel | Mehler kernel eigenfunction expansion |

## Proved Results (formerly axioms)

The following were axioms and are now fully proved theorems:

### Nuclear tensor products (8 proved)
- `nuclearTensorProduct_mapCLM_general` — via Schauder basis coefficient mapping (general version)
- `nuclearTensorProduct_mapCLM_general_pure` — action on pure tensors (general version)
- `nuclearTensorProduct_mapCLM` — via Schauder basis coefficient mapping
- `nuclearTensorProduct_mapCLM_pure` — via DM expansion + `tsum_mul_tsum`
- `nuclearTensorProduct_mapCLM_id` — via biorthogonality + `tsum_eq_single`
- `nuclearTensorProduct_mapCLM_comp` — via DM expansion + `mapCLM_pure`
- `nuclearTensorProduct_swapCLM` — via Cantor pair permutation
- `nuclearTensorProduct_swapCLM_pure` — via coefficient commutativity

### Periodization (6 proved)
- `periodizeCLM` — axiom → def (tsum + summability + smoothness)
- `periodizeCLM_apply` — proved by rfl
- `periodize_sobolevSeminorm_le` — via iteratedDerivWithin_tsum + Schwartz decay + 1/j² summability
- `periodizeCLM_comp_schwartzTranslation` — from pointwise formula + ext
- `periodizeCLM_comp_schwartzReflection` — from pointwise formula + Equiv.tsum_eq
- `periodizeCLM_eq_on_large_period` — from tsum_eq_single + support argument

### Fourier multiplier (7 proved)
- `fourierMultiplier_preserves_real` — via Fourier conjugation symmetry + integral_neg_eq_self
- `fourierMultiplierCLM_translation_comm` — via Fourier shift theorem + smul_comm
- `fourierMultiplierCLM_even_reflection_comm` — via Fourier reflection (linear isometry) + evenness
- `resolventMultiplierCLM_injective` — via Fourier inversion + symbol positivity
- `realFourierMultiplierCLM_comp` — from Mathlib `compL` + `preserves_real`
- `realFourierMultiplierCLM_translation_comm` — from complex translation comm
- `realFourierMultiplierCLM_even_reflection_comm` — from complex reflection comm

### Schwartz Fourier analysis (3 proved — new module `SchwartzFourier/`)
- `schwartzLaplaceEvalCLM` — axiom → def (constructed via `laplaceEvalLinear` + continuity from `toLpCLM`)
- `schwartzLaplaceEvalCLM_apply` — axiom → theorem (definitional `rfl`)
- `schwartzLaplace_uniformBound` — axiom → theorem (via `toLpCLM` + `Seminorm.bound_of_continuous` + L¹ norm identity)
- Also proved: `resolventSymbol_antitone`, `resolventQuotientSymbol_le_one`/`_pos`/`_even`, `resolventSymbol_mul_quotient` (factorization identity)

### Mass operator construction (1 proved + 4 new theorems)
- `cylinderMassOperator` — axiom → def via `ntpSliceSchwartz` + `resolventMultiplierCLM` + `nuclear_ell2_embedding_from_decay`
- `massOperatorCoord` — m-th coordinate functional (def)
- `massOperatorCoord_decay` — nuclear decay bound (proved from Cantor pairing + coeff_decay + slice a-decay)
- `cylinderMassOperator_coord/formula` — coordinate access theorems

### Laplace embedding construction (1 proved + 3 new theorems)
- `cylinderLaplaceEmbedding` — axiom → def via `schwartzLaplaceEvalCLM` + `ntpSliceSchwartz` + `nuclear_ell2_embedding_from_decay`
- `laplaceEmbeddingCoord` — a-th coordinate functional (def)
- `laplaceEmbeddingCoord_decay` — nuclear decay bound (proved from uniform Laplace bound + inverse Hermite + slice a-decay)
- `cylinderLaplaceEmbedding_coord` — coordinate access theorem

### Green's function (2 proved)
- `cylinderGreen_continuous_seminorm_bound` — $G(f,f) \leq q(f)^2$ via `normSeminorm`
- `cylinderGreen_pos` — $G(f,f) > 0$ for $f \neq 0$, via `cylinderMassOperator_injective` (resolvent injectivity + CLE chain)

### Method of images (4 proved)
- `torusGreen_uniform_bound` — proved from `embed_l2_uniform_bound` + `greenFunctionBilinear_le`
- `l2InnerProduct_pure` — ℓ² factors for NTP pure tensors (Fubini + Cantor reindex)
- `l2InnerProduct_swap` — swap preserves ℓ² (permutation reindex)
- `l2InnerProduct_le_seminorm` — ℓ² bounded by DM seminorm (coeff_decay)

### Embedding (1 proved)
- `cylinderToTorusEmbed` — axiom → def (swap ∘ (id ⊗ periodize))

### Lattice convergence (all proved)
- `lattice_green_tendsto_continuum_pure` — via Tannery's theorem
- `lattice_green_tendsto_continuum` — bilinear extension via DM expansion
- All 1D heat kernel convergence results

### FKG inequality (all proved)
- `ahlswede_daykin_ennreal` — ENNReal n-dimensional induction
- `gaussian_fkg_lattice_condition` — from AD theorem
- `fkg_perturbed`, `fkg_lattice_gaussian`, `fkg_truncation_dct` — proved chain

### Green's function invariance (all proved)
- `greenFunctionBilinear_reflection_pure` — mode-partner involution
- `greenFunctionBilinear_translation_pure` — paired translation
- `greenFunctionBilinear_invariant_of_pure` — DM expansion

### Fourier coefficients (all 6 proved)
- All `fourierCoeffReal_circle{Translation,Reflection}_{zero,cos,sin}` proved

## Build

```bash
lake build
```

The project depends on Mathlib (fetched automatically by lake).

## References

- Gel'fand-Vilenkin, *Generalized Functions Vol. 4* — nuclear spaces
- Bogachev, *Gaussian Measures* — Gaussian measures on Fréchet spaces
- Holley (1974), Fortuin-Kasteleyn-Ginibre (1971) — FKG inequality
- Trèves, *Topological Vector Spaces* — tensor product CLMs
- Stein-Weiss, *Fourier Analysis* — periodization, Fourier multipliers
- Reed-Simon I — Hilbert-Schmidt operators, resolvent
- Osterwalder-Schrader (1973, 1975) — OS axioms
