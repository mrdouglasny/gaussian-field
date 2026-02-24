# FKG Proof Plan — Implementation Status

**Date**: 2026-02-24 (updated)
**Status**: Core implementation complete. Both main theorems sorry-free.

---

## Current State (Implemented)

### File: `Lattice/FKG.lean`

**Proved theorems (no sorry):**
- `chebyshev_integral_inequality` — 1D FKG (base case)
- `fkg_lattice_condition_mul` — product of FKG-lattice densities is FKG-lattice
- `fkg_lattice_condition_single_site` — exp(-V) satisfies FKG when V is single-site
- `fkg_lattice_condition_of_submodular` — exp(-submodular V) satisfies FKG
- `single_coord_sup_inf_sum` — v(a⊔b) + v(a⊓b) = v(a) + v(b)
- `sup_inf_mul_add_le` — max-min product inequality (4-case algebra)
- `quadraticForm_submodular_of_nonpos_offDiag` — Q non-pos off-diag → ½⟨φ,Qφ⟩ submodular
- `gaussianDensity_fkg_lattice_condition` — Gaussian density satisfies FKG lattice condition
- `gaussianDensity_nonneg` — Gaussian density ≥ 0
- `field_basis_decomposition` — φ = Σ φ(y) · δ_y
- `massOperator_apply_eq_sum` — (Qφ)(x) = Σ Q(x,y) · φ(y)
- `massOperator_bilinear_eq_sum` — ⟨φ,Qφ⟩ = Σ Σ Q(x,y) · φ(x) · φ(y)
- `liftToConfig` / `liftToConfig_delta` / `config_eq_liftToConfig` — field↔config correspondence
- `isFieldMonotone_lift` — monotonicity transfer through lift
- **`gaussian_fkg_lattice_condition`** — FKG for Gaussian measure (**sorry-free**)
- **`fkg_perturbed`** — FKG for single-site perturbations (**sorry-free**)

**Axioms (6):**

| # | Axiom | Role | Provability |
|---|-------|------|-------------|
| 1 | `fkg_from_lattice_condition` | Core FKG: lattice condition → correlation inequality | Hard (induction + Holley) |
| 2 | `massOperator_offDiag_nonpos` | Q has non-positive off-diagonal entries | Easy (from `finiteLaplacianFun`) |
| 3 | `latticeGaussianMeasure_density_integral` | Density bridge: E_μ[F] = ∫Fρ/∫ρ | Hard (measure theory) |
| 4 | `gaussianDensity_integrable` | exp(-½⟨φ,Qφ⟩) is Lebesgue-integrable | Medium (Gaussian integral) |
| 5 | `gaussianDensity_integral_pos` | ∫exp(-½⟨φ,Qφ⟩) > 0 | Easy (from #4 + positivity) |
| 6 | `integrable_mul_gaussianDensity` | F·ρ is Lebesgue-integrable | Medium (abs. continuity) |

---

## Proof Architecture (Implemented)

```
massOperator_offDiag_nonpos [axiom 2]
    ↓
quadraticForm_submodular_of_nonpos_offDiag [proved]
    ↓
gaussianDensity_fkg_lattice_condition [proved]
    ↓
fkg_from_lattice_condition [axiom 1] + density bridge [axiom 3]
  + integrable_mul_gaussianDensity [axiom 6]
  + gaussianDensity_integrable [axiom 4]
  + gaussianDensity_integral_pos [axiom 5]
    ↓
gaussian_fkg_lattice_condition [PROVED — sorry-free]
    ↓
  + fkg_lattice_condition_single_site [proved]
  + fkg_lattice_condition_mul [proved]
    ↓
fkg_perturbed [PROVED — sorry-free]
```

---

## Remaining Work: Axiom Reduction

### Priority 1: Easy axioms to prove

**`massOperator_offDiag_nonpos`** (axiom 2)
- Should be provable from `finiteLaplacianFun` definition
- The mass term m²·I is diagonal; -Δ has entries -a⁻² for neighbors, 0 otherwise
- Estimated: ~40 lines

**`gaussianDensity_integral_pos`** (axiom 5)
- Follows from `gaussianDensity_integrable` + `gaussianDensity_nonneg` + continuity
- Estimated: ~20 lines (if `gaussianDensity_integrable` is proved)

### Priority 2: Medium axioms

**`gaussianDensity_integrable`** (axiom 4)
- Standard Gaussian integral on ℝ^n
- Could use Fubini + 1D `gaussianReal` integrability from Mathlib
- Estimated: ~60 lines

**`integrable_mul_gaussianDensity`** (axiom 6)
- Follows from density bridge (absolute continuity of Gaussian measure)
- If the Gaussian measure has density ρ/Z w.r.t. Lebesgue, then
  Integrable F μ → Integrable (F·ρ) Lebesgue
- Estimated: ~40 lines (given density bridge)

### Priority 3: Hard axioms

**`latticeGaussianMeasure_density_integral`** (axiom 3)
- Bridge from pushforward construction to explicit density
- Requires: Gaussian COV on ℝ^n, Degenne's `multivariateGaussian`, `map_linearMap_addHaar`
- Estimated: ~200 lines

**`fkg_from_lattice_condition`** (axiom 1)
- Core FKG theorem (Holley 1974)
- Proof by induction on |ι| requires:
  - `fkg_lattice_condition_marginal` — marginal preserves FKG (hard)
  - `monotone_condexp_weighted` — Holley's criterion (hard)
  - `fin_equiv_split` — coordinate splitting infrastructure (medium)
- Estimated: ~500 lines total
- Alternative: keep as axiom (independently verifiable mathematical fact)

---

## Mathlib Tools Available

- `gaussianReal` with density — `Mathlib.Probability.Distributions.Gaussian.Real`
- `map_linearMap_addHaar_eq_smul_addHaar` — linear COV for Lebesgue
- `Equiv.piEquivPiSubtypeProd` — splitting `(ι → ℝ) ≃ ((↑s → ℝ) × (↑sᶜ → ℝ))`
- `Pi.sup_apply` / `Pi.inf_apply` — componentwise lattice (used in proofs)
- `integral_prod` — Fubini theorem
- `Fintype.equivFin` — `ι ≃ Fin n` for induction

## External Resources

- Degenne et al., "Brownian motion in Lean" (arXiv:2511.20118)
  - `multivariateGaussian`, characteristic function, covariance
  - Missing: explicit density via `withDensity`

## References

- Fortuin-Kasteleyn-Ginibre (1971), "Correlation inequalities"
- Holley (1974), "Remarks on the FKG inequalities"
- Preston (1974), "A generalization of the FKG inequalities"
- Pitt (1982), "Positively correlated normal variables are associated"
- Glimm-Jaffe, *Quantum Physics*, §19
