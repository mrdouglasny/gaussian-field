# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, the FKG inequality, and cylinder QFT
infrastructure for use by downstream projects (pphi2, OSforGFF).

**7 axioms, 0 sorries** (active build, excluding `future/`)

*Updated 2026-03-25.*

## Active Axiom Inventory (7 axioms)

### Periodization (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 1 | `periodize_sobolevSeminorm_le` | SchwartzNuclear/Periodization | Sobolev seminorm bound: $\lVert \text{periodize}\,h \rVert_{H^k} \leq C \cdot p(h)$ for Schwartz seminorms $p$. Continuity bound for `periodizeCLM`. |

Note: `periodizeCLM` is now a **definition** (was axiom). `periodizeCLM_apply` proved by rfl. `periodize_summable`, `periodize_smooth`, `iteratedFDeriv_mul_schwartz_decay` all **proved**. The three intertwining properties (`_comp_schwartzTranslation`, `_comp_schwartzReflection`, `_eq_on_large_period`) are all **proved theorems**.

### Fourier multiplier properties (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 2 | `fourierMultiplier_preserves_real` | Cylinder/FourierMultiplier | Even real-valued Fourier multiplier $M_\sigma$ maps real Schwartz functions to real Schwartz functions. Uses Fourier conjugation symmetry. |

Note: `fourierMultiplierCLM_translation_comm` is now a **proved theorem** (Fourier shift + smul_comm). `fourierMultiplierCLM_even_reflection_comm` is now a **proved theorem** (Fourier reflection via linear isometry). `resolventMultiplierCLM_injective` is a **proved theorem** (Fourier inversion). The three real versions (`realFourierMultiplierCLM_comp`, `_translation_comm`, `_even_reflection_comm`) are all **proved theorems**.

### Cylinder Green's function (2 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 4 | `resolventSchwartz_uniformBound` | Cylinder/MassOperatorConstruction | Resolvent Schwartz seminorm bounds uniform in $\omega \geq m$. Symbol $(p^2+\omega^2)^{-1/2}$ is decreasing in $\omega$. |
| 5 | `cylinderMassOperator_equivariant_of_heat_comm` | Cylinder/GreenFunction | Heat kernel equivariance principle: if CLM $S$ commutes with $e^{-tA}$ for all $t \geq 0$, then $T$ intertwines $S$ with an isometry $U$ on $\ell^2$. |

Note: `cylinderMassOperator` is now a **definition** (constructed from `ntpSliceSchwartz` + `resolventMultiplierCLM` + `nuclear_ell2_embedding_from_decay`). `cylinderGreen_pos` is a **proved theorem** from `cylinderMassOperator_injective`. `cylinderGreen_continuous_seminorm_bound` is a **proved theorem**.

### Cylinder reflection positivity (2 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 6 | `cylinderLaplaceEmbedding` | Cylinder/ReflectionPositivity | The Laplace embedding $\Lambda : \text{CylinderTF}(L) \to \ell^2$. Maps each spatial mode to its Laplace transform at the resolvent frequency. |
| 7 | `cylinderGreen_reflection_eq_laplaceNorm` | Cylinder/ReflectionPositivity | Laplace factorization: $G(f, \Theta f) = \lVert \Lambda f \rVert^2$ for positive-time $f$. Resolvent kernel factors as $e^{-\omega t} \cdot e^{\omega s} / (2\omega)$ for $t > 0 > s$. |

Note: `cylinderGreen_reflection_positive` ($G(f,\Theta f) \geq 0$) is a **proved theorem** from the Laplace factorization identity. `cylinderGreen_reflection_strict_positive` was removed as a dead axiom.

### Method of images (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 8 | `embed_l2_uniform_bound` | Cylinder/MethodOfImages | $\lVert \text{embed}\,f \rVert_{\ell^2}^2 \leq q(f)^2$ uniformly in $L_t \geq 1$. Uniform ℓ² bound for the periodization embedding. |

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

### Periodization (5 proved)
- `periodizeCLM` — axiom → def (now constructed from `periodize_summable` + `periodize_smooth`)
- `periodizeCLM_apply` — proved by rfl
- `periodizeCLM_comp_schwartzTranslation` — from pointwise formula + `ext`
- `periodizeCLM_comp_schwartzReflection` — from pointwise formula + `Equiv.tsum_eq`
- `periodizeCLM_eq_on_large_period` — from `tsum_eq_single` + support argument

### Fourier multiplier (6 proved)
- `fourierMultiplierCLM_translation_comm` — via Fourier shift theorem + smul_comm
- `fourierMultiplierCLM_even_reflection_comm` — via Fourier reflection (linear isometry) + evenness
- `resolventMultiplierCLM_injective` — via Fourier inversion + symbol positivity
- `realFourierMultiplierCLM_comp` — from Mathlib `compL` + `preserves_real`
- `realFourierMultiplierCLM_translation_comm` — from complex translation comm
- `realFourierMultiplierCLM_even_reflection_comm` — from complex reflection comm

### Mass operator construction (1 proved + 4 new theorems)
- `cylinderMassOperator` — axiom → def via `ntpSliceSchwartz` + `resolventMultiplierCLM` + `nuclear_ell2_embedding_from_decay`
- `massOperatorCoord` — m-th coordinate functional (def)
- `massOperatorCoord_decay` — nuclear decay bound (proved from Cantor pairing + coeff_decay + slice a-decay)
- `cylinderMassOperator_coord/formula` — coordinate access theorems

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
