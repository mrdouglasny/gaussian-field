# Gaussian-Field Axiom Proof Plans

**Generated**: 2026-02-25 via Gemini deep think review
**Total**: 2 axioms (current), 0 sorries

## Priority Order

### P0: Density Master Theorem (completed)

Target theorem (in `GaussianField/Density.lean`):

`latticeGaussianMeasure_eq_normalizedGaussianDensityMeasure`

Statement shape:
`(latticeGaussianMeasure ...).map (evalMap d N) = normalizedGaussianDensityMeasure d N a mass`.

This single measure-equality theorem should derive both:

1. `latticeGaussianMeasure_density_integral` (integral rewrite by `integral_map`)
2. `integrable_mul_gaussianDensity` (integrability transfer via equality + withDensity form)

Proof decomposition:

1. Pushforward charFun:
   compute charFun of `(latticeGaussianMeasure ...).map evalMap` via
   `GaussianField.charFun` and the spectral covariance identity.
2. Density charFun:
   compute charFun of `normalizedGaussianDensityMeasure` using Gaussian Fourier
   transform in finite dimensions.
3. Normalization:
   show density normalizing constant is finite and nonzero
   (`gaussianDensityNormConst` lemmas + positivity/integrability).
4. Uniqueness:
   apply `Measure.ext_of_charFun` to conclude equality.
5. Corollaries:
   derive #17 and #18 as theorems (remove their axiom declarations).

Relation to `pairing_is_gaussian`:

Yes. Once the master theorem is proved, pushing forward the density measure by a
linear functional gives an alternative route to 1D Gaussian marginals. It can
recover `pairing_is_gaussian` for finite-lattice evaluations and should align
with the existing charFun proof in `GaussianField/Properties.lean`.

### Tier 1: EASY (standard Mathlib applications, likely provable now)

#### 1. `integral_norm_tsum_le_tsum_integral_norm` (PositionKernel.lean:1068, private)

**Statement**: `integral ‖sum' f_j‖ <= sum' integral ‖f_j‖`

**Plan**:
1. Pointwise triangle inequality: `norm_tsum_le_tsum_norm` gives `‖sum' f_j(a)‖ <= sum' ‖f_j(a)‖`
2. Apply `integral_mono` to integrate both sides
3. RHS: apply `integral_tsum` (Tonelli for series) since `‖f_j‖ >= 0`

**Key Mathlib**: `norm_tsum_le_tsum_norm`, `integral_mono`, `integral_tsum`

---

#### 2. `integrable_tsum_of_summable_integral_norm` (PositionKernel.lean:1076, private)

**Statement**: If `sum integral ‖f_j‖ < infinity`, then `sum' f_j` is integrable.

**Plan**:
1. Use `MeasureTheory.integrable_tsum` — this is exactly the statement
2. Main hypothesis: `integral (sum' ‖f_j‖) < infinity`
3. Rewrite via `integral_tsum` (Tonelli): `integral (sum' ‖f_j‖) = sum' integral ‖f_j‖`
4. The hypothesis `hF_sum` provides exactly this

**Key Mathlib**: `MeasureTheory.integrable_tsum`, `integral_tsum`

---

#### 3. `integrable_truncation_mul` (FKG.lean:747)

**Statement**: If `F*rho` integrable, then `max(F,-n)*rho` integrable.

**Plan**:
1. Prove helper: `|max(a, -n)| <= |a|` for all real `a`, `n >= 0`
   - Case `a >= -n`: `max(a,-n) = a`, trivial
   - Case `a < -n`: `max(a,-n) = -n`, and `n < |a|` since `a < -n`
2. Therefore `‖max(F x, -n) * rho x‖ <= ‖F x * rho x‖` pointwise
3. Apply `Integrable.mono` with dominator `F*rho`

**Key Mathlib**: `Integrable.mono`

---

#### 4. `integrable_truncation_prod_mul` (FKG.lean:752)

**Statement**: If `F*G*rho` integrable, then `max(F,-n)*max(G,-n)*rho` integrable.

**Plan**: Same as #3 but apply `|max(a,-n)| <= |a|` twice:
`|max(F,-n)| * |max(G,-n)| * |rho| <= |F| * |G| * |rho|`

**Key Mathlib**: `Integrable.mono`

---

#### 5. `fkg_truncation_dct` (FKG.lean:732)

**Statement**: `integral (max(F,-n) * rho)` converges to `integral (F * rho)` as `n -> infinity`.

**Plan**:
1. Define sequence `g_n(x) = max(F(x), -n) * rho(x)`
2. **Pointwise convergence**: `lim max(a, -n) = a` for all `a`
3. **Dominator**: `|g_n(x)| <= |F(x) * rho(x)|` (from #3's helper)
4. **Integrability of dominator**: hypothesis `hFrho`
5. Apply `tendsto_integral_of_dominated_convergence`

**Key Mathlib**: `MeasureTheory.tendsto_integral_of_dominated_convergence`

---

#### 6. `fkg_truncation_dct_prod` (FKG.lean:739)

**Statement**: Same as #5 but for `max(F,-n)*max(G,-n)*rho -> F*G*rho`.

**Plan**: Identical to #5 with dominator `|F*G*rho|` and pointwise convergence of the product.

**Key Mathlib**: `MeasureTheory.tendsto_integral_of_dominated_convergence`

---

#### 7. `integral_empty_pi` (FKG.lean:529)

**Statement**: `integral f = f(fun e => e.elim)` over `(Empty -> R)`.

**Plan**:
1. `(Empty -> R)` is `Unique` (has exactly one element: the empty function)
2. The volume measure on a `Unique` type is `Measure.dirac` at the unique point
3. Apply `integral_dirac`

**Key Mathlib**: `integral_dirac`, `Function.isEmpty_pi`

---

### Tier 2: MEDIUM (clear path, moderate formalization effort)

#### 8. `fubini_pi_decomp` (FKG.lean:507)

**Statement**: Fubini for `R^iota` decomposed as `R x R^{iota\{i}}`.

**Plan**:
1. Define equiv `e := Function.piEquivPiSubtypeProd iota (fun _ => R) i`
2. Show `e` is measure-preserving (`volume` on Pi type = product measure)
3. Apply `MeasurePreserving.integral_comp` to rewrite integral
4. Apply `integral_integral_swap` (Fubini) on the product space

**Key Mathlib**: `Function.piEquivPiSubtypeProd`, `integral_integral_swap`, `MeasurePreserving.integral_comp`
**Blocker**: May need to prove `MeasurePreserving` instance for `piEquivPiSubtypeProd`

---

#### 9. `integrable_marginal` (FKG.lean:514)

**Statement**: Marginal of nonneg integrable function is integrable.

**Plan**:
1. Apply `Integrable.integral_fst` (or its Pi-type variant)
2. Nonnegativity simplifies: `‖f‖ = f`

**Key Mathlib**: `Integrable.integral_fst`
**Blocker**: API friction with Pi types vs product types

---

#### 10. `integrable_fiber_ae` (FKG.lean:522)

**Statement**: Fiber of integrable function is integrable a.e.

**Plan**: Apply `MeasureTheory.integrable_ae_of_integrable` (Fubini conclusion).

**Key Mathlib**: `integrable_ae_of_integrable`
**Blocker**: Same Pi-type API issues as #9

---

#### 11. `circleHeatKernel_pos` (PositionKernel.lean:597)

**Statement**: Circle heat kernel `> 0` for `t > 0`.

**Plan** (via Poisson summation):
1. Write kernel as Fourier series: `K(t,x) = sum_{n in Z} exp(-n^2 t) exp(i n x)`
2. Apply Poisson summation: `= sum_{k in Z} C_t * exp(-(x-2pi*k)^2 / (4t))`
3. Each term is strictly positive for `t > 0`
4. Sum of positive terms is positive

**Key Mathlib**: `PoissonSummation`, `fourier_transform_gaussian`
**Blocker**: Constant management, matching conventions

---

#### 12. `cylinderEval_summable` (PositionKernel.lean:1056)

**Statement**: Eigenfunction expansion of cylinder test functions converges.

**Plan**:
1. Test functions are smooth => Fourier coefficients decay rapidly
2. Integration by parts: each derivative brings factor of `k_j`
3. For `C^m` function: `|c_k| = O(‖k‖^{-m})`
4. Rapid decay => absolute convergence of series

**Key Mathlib**: Fourier series API
**Blocker**: Multivariate Fourier series API may be incomplete

---

#### 13-14. `latticeEnum_norm_bound` / `latticeEnum_index_bound` (RapidDecayLattice.lean:208,213)

**Status**: Completed.

Both polynomial bounds are now proved by induction on pairing depth using:
- `Nat.unpair` monotonicity for inverse growth.
- `Nat.pair_lt_max_add_one_sq` plus explicit `ℤ ↔ ℕ` growth bounds for forward growth.

---

#### 15. `latticeRapidDecayEquiv` (RapidDecayLattice.lean)

**Status**: Completed.

Proof now implemented as a constructive continuous linear equivalence using
`latticeEnum` reindexing plus the two polynomial bound theorems
`latticeEnum_norm_bound` and `latticeEnum_index_bound`.

---

### Tier 3: HARD (major formalization effort)

#### 16. `ad_marginal_preservation_ae` (FKG.lean:567)

**Statement**: Ahlswede-Daykin inequality preserved by marginalization.

**Plan**: Apply 1D AD to fibers, then Fubini to reassemble. This is the standard induction step for multi-dim AD from 1D.

**Technical gap**: The current 1D AD theorem (`ahlswede_daykin_one_dim`) is pointwise (∀ x y),
but after Fubini the induction step naturally gives only a.e.-in-(x,y) data.
Need either:
1. An a.e. version of the 1D AD theorem, or
2. A lemma upgrading the a.e. fiber condition to pointwise on a full-measure set
   (choose representatives, show the AD hypothesis holds pointwise on the product
   of full-measure sets).

**Blocker**: This a.e.-to-pointwise bridge, NOT Prekopa-Leindler.

---

#### 17. `latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure` (Density.lean)

**Statement**: Master density law:
`(latticeGaussianMeasure ...).map evalMap = normalizedGaussianDensityMeasure`.

**Plan**:
1. Compute `charFun` of field-law pushforward via `GaussianField.charFun` and spectral covariance.
2. Compute `charFun` of normalized Gaussian density measure by finite-dimensional Gaussian Fourier transform.
3. Normalize and prove finiteness/nonzero of the density constant.
4. Apply `Measure.ext_of_charFun`.

**Note**: Former density bridge and integrability-transfer axioms are now theorems derived from this master statement.

---

#### 18. `gaussian_moment_ratio_bound` — **ELIMINATED**

**Former location**: Hypercontractive.lean:152

**Resolution**: Proved for even integer p = 2m via double-factorial combinatorics
in `GaussianField/HypercontractiveNat.lean`. The axiom and its Gamma-based
consumers have been removed from `Hypercontractive.lean`. The full chain
(`hypercontractive_1d`, `hypercontractive_gaussianReal`, `gaussian_hypercontractive`)
now lives in `HypercontractiveNat.lean` with additional hypotheses
`(m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m)`.

---

#### 19. `mehlerKernel_eq_series` (PositionKernel.lean:44)

**Statement**: Mehler kernel = eigenfunction expansion of harmonic oscillator.

**Plan**:
1. Define quantum harmonic oscillator `H = -d^2/dx^2 + x^2`
2. Prove Hermite functions are eigenfunctions with eigenvalues `2k+1`
3. Prove completeness of Hermite functions in L^2(R)
4. Apply spectral theorem to define `exp(-tH)` and identify kernel

**Blocker**: **Unbounded operator spectral theory missing from Mathlib**. This is the hardest axiom.
