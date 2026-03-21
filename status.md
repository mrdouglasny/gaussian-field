# gaussian-field Project Status

## Overview

The gaussian-field library provides Gaussian free field theory on nuclear spaces,
lattice field theory infrastructure, the FKG inequality, and cylinder QFT
infrastructure for use by downstream projects (pphi2, OSforGFF).

**14 axioms, 0 sorries** (active build, excluding `future/`)

*Updated 2026-03-21.*

## Active Axiom Inventory (14 axioms)

### Nuclear tensor product infrastructure (2 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 1 | `nuclearTensorProduct_mapCLM_general` | Nuclear/GeneralMapCLM | NTP functor for CLMs between different DM spaces: $(T_1 \otimes T_2) : \text{NTP}(E_1,E_2) \to \text{NTP}(F_1,F_2)$ |
| 2 | `nuclearTensorProduct_mapCLM_general_pure` | Nuclear/GeneralMapCLM | Action on pure tensors: $(T_1 \otimes T_2)(\text{pure}(e_1,e_2)) = \text{pure}(T_1 e_1, T_2 e_2)$ |

Note: The endomorphism versions (`mapCLM`, `mapCLM_pure`, `mapCLM_id`, `mapCLM_comp`, `swapCLM`, `swapCLM_pure`) are all **proved theorems** in Nuclear/TensorProductFunctorAxioms.lean.

### Periodization (2 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 3 | `periodizeCLM` | SchwartzNuclear/Periodization | The periodization CLM $\mathcal{S}(\mathbb{R}) \to C^\infty(S^1_L)$: $(\text{periodize}_L h)(t) = \sum_{k \in \mathbb{Z}} h(t + kL)$ |
| 4 | `periodizeCLM_apply` | SchwartzNuclear/Periodization | Pointwise formula for periodization as a tsum |

Note: The three properties (`_comp_schwartzTranslation`, `_comp_schwartzReflection`, `_eq_on_large_period`) are all **proved theorems** from the pointwise formula.

### Fourier multiplier properties (3 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 5 | `fourierMultiplier_preserves_real` | Cylinder/FourierMultiplier | Even real-valued Fourier multiplier $M_\sigma$ maps real Schwartz functions to real Schwartz functions. Uses Fourier conjugation symmetry. |
| 6 | `fourierMultiplierCLM_translation_comm` | Cylinder/FourierMultiplier | $M_\sigma(T_\tau f) = T_\tau(M_\sigma f)$ on $\mathcal{S}(\mathbb{R}, \mathbb{C})$. Phase factor commutativity. |
| 7 | `fourierMultiplierCLM_even_reflection_comm` | Cylinder/FourierMultiplier | $M_\sigma(\Theta f) = \Theta(M_\sigma f)$ for even $\sigma$ on $\mathcal{S}(\mathbb{R}, \mathbb{C})$ |

Note: The three real versions (`realFourierMultiplierCLM_comp`, `_translation_comm`, `_even_reflection_comm`) are all **proved theorems** from these + Mathlib's `fourierMultiplierCLM_compL_fourierMultiplierCLM`.

### Cylinder Green's function (3 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 8 | `cylinderMassOperator` | Cylinder/GreenFunction | The mass operator $T = A^{-1/2} : \text{CylinderTF}(L) \to \ell^2$. GNS map for the covariance: $\langle Tf, Tg \rangle = G(f,g)$. Decomposes by spatial Fourier mode via `resolventMultiplierCLM`. |
| 9 | `cylinderGreen_pos` | Cylinder/GreenFunction | $G_L(f,f) > 0$ for $f \neq 0$. Injectivity of the mass operator (resolvent has non-vanishing symbol). |
| 10 | `cylinderMassOperator_equivariant_of_heat_comm` | Cylinder/GreenFunction | Heat kernel equivariance principle: if CLM $S$ commutes with $e^{-tA}$ for all $t \geq 0$, then $T$ intertwines $S$ with an isometry $U$ on $\ell^2$. |

Note: `cylinderGreen_continuous_seminorm_bound` is a **proved theorem** ($G(f,f) = \lVert Tf \rVert^2 \leq q(f)^2$ via `normSeminorm`). The three equivariance corollaries (spatial translation, time translation, time reflection) are **proved theorems** from the general principle + heat semigroup commutation.

### Cylinder reflection positivity (3 axioms)

| # | Name | File | Description |
|---|------|------|-------------|
| 11 | `cylinderLaplaceEmbedding` | Cylinder/ReflectionPositivity | The Laplace embedding $\Lambda : \text{CylinderTF}(L) \to \ell^2$. Maps each spatial mode to its Laplace transform at the resolvent frequency. |
| 12 | `cylinderGreen_reflection_eq_laplaceNorm` | Cylinder/ReflectionPositivity | Laplace factorization: $G(f, \Theta f) = \lVert \Lambda f \rVert^2$ for positive-time $f$. Resolvent kernel factors as $e^{-\omega t} \cdot e^{\omega s} / (2\omega)$ for $t > 0 > s$. |
| 13 | `cylinderGreen_reflection_strict_positive` | Cylinder/ReflectionPositivity | Strict RP: $G(f, \Theta f) > 0$ for nonzero positive-time $f$. From injectivity of Laplace transform on $(0,\infty)$. |

Note: `cylinderGreen_reflection_positive` ($G(f,\Theta f) \geq 0$) is a **proved theorem** from the Laplace factorization identity.

### Method of images (1 axiom)

| # | Name | File | Description |
|---|------|------|-------------|
| 14 | `embed_l2_uniform_bound` | Cylinder/MethodOfImages | $\lVert \text{embed}\,f \rVert_{\ell^2}^2 \leq q(f)^2$ uniformly in $L_t \geq 1$. Uniform ℓ² bound for the periodization embedding. |

Note: `torusGreen_uniform_bound` is now a **proved theorem** from `embed_l2_uniform_bound` + `greenFunctionBilinear_le`. Also proved: `l2InnerProduct_pure`, `l2InnerProduct_swap`, `l2InnerProduct_le_seminorm`.

Note: `cylinderToTorusEmbed` is a **definition** (not axiom), and `cylinderGreen_continuous_seminorm_bound` is a **proved theorem**.

## Inactive / Future Axioms (not counted)

| Name | File | Description |
|------|------|-------------|
| `schwartz_dyninMityaginSpace_axiom` | GaussianField.lean | Fallback axiom (commented out). Proved instance used instead. |
| `NuclearSpaceStd` | future/KolmogorovGaussian | Alternative Gaussian construction via Cipollina's framework |
| `kolmogorov_gaussian_measure` | future/KolmogorovGaussian | Kolmogorov-Minlos existence |
| `mehlerKernel_eq_series` | future/PositionKernel | Mehler kernel eigenfunction expansion |

## Proved Results (formerly axioms)

The following were axioms and are now fully proved theorems:

### Nuclear tensor products (6 proved)
- `nuclearTensorProduct_mapCLM` — via Schauder basis coefficient mapping
- `nuclearTensorProduct_mapCLM_pure` — via DM expansion + `tsum_mul_tsum`
- `nuclearTensorProduct_mapCLM_id` — via biorthogonality + `tsum_eq_single`
- `nuclearTensorProduct_mapCLM_comp` — via DM expansion + `mapCLM_pure`
- `nuclearTensorProduct_swapCLM` — via Cantor pair permutation
- `nuclearTensorProduct_swapCLM_pure` — via coefficient commutativity

### Periodization (3 proved)
- `periodizeCLM_comp_schwartzTranslation` — from pointwise formula + `ext`
- `periodizeCLM_comp_schwartzReflection` — from pointwise formula + `Equiv.tsum_eq`
- `periodizeCLM_eq_on_large_period` — from `tsum_eq_single` + support argument

### Fourier multiplier (3 proved)
- `realFourierMultiplierCLM_comp` — from Mathlib `compL` + `preserves_real`
- `realFourierMultiplierCLM_translation_comm` — from complex translation comm
- `realFourierMultiplierCLM_even_reflection_comm` — from complex reflection comm

### Green's function (1 proved)
- `cylinderGreen_continuous_seminorm_bound` — $G(f,f) \leq q(f)^2$ via `normSeminorm`

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
