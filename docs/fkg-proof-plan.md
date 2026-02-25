# FKG Proof Plan — Implementation Status

**Date**: 2026-02-24 (updated)
**Status**: Core implementation complete. Both main theorems sorry-free. 2 axioms remain (down from 6).

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
- `massOperator_offDiag_nonpos` — Q has non-positive off-diagonal entries (**was axiom**)
- `gaussianDensity_integrable` — exp(-½⟨φ,Qφ⟩) is Lebesgue-integrable (**was axiom**)
- `gaussianDensity_integral_pos` — ∫exp(-½⟨φ,Qφ⟩) > 0 (**was axiom**)
- `field_basis_decomposition` — φ = Σ φ(y) · δ_y
- `massOperator_apply_eq_sum` — (Qφ)(x) = Σ Q(x,y) · φ(y)
- `massOperator_bilinear_eq_sum` — ⟨φ,Qφ⟩ = Σ Σ Q(x,y) · φ(x) · φ(y)
- `liftToConfig` / `liftToConfig_delta` / `config_eq_liftToConfig` — field↔config correspondence
- `isFieldMonotone_lift` — monotonicity transfer through lift
- **`gaussian_fkg_lattice_condition`** — FKG for Gaussian measure (**sorry-free**)
- **`fkg_perturbed`** — FKG for single-site perturbations (**sorry-free**)

**Axioms (2, down from 6):**

| # | Axiom | Role | Provability |
|---|-------|------|-------------|
| 1 | `fkg_from_lattice_condition` | Core FKG: lattice condition → correlation inequality | Hard (induction + Holley) |
| 2 | `latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure` | Master density law: field-law pushforward = normalized density measure | Hard (measure theory) |

---

## Proof Architecture (Implemented)

```
massOperator_offDiag_nonpos [PROVED]
    ↓
quadraticForm_submodular_of_nonpos_offDiag [proved]
    ↓
gaussianDensity_fkg_lattice_condition [proved]
    ↓
fkg_from_lattice_condition [axiom 1]
  + latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure [axiom 2]
  + derived density bridge + integrability transfer theorems
  + gaussianDensity_integrable [PROVED]
  + gaussianDensity_integral_pos [PROVED]
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

### Priority 1: Hard axiom

**`latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure`** (axiom 2)
- Master density theorem from which both former density axioms are now derived.
- Bridge from pushforward construction to explicit normalized density.
- Requires: characteristic-function computation on both sides + uniqueness.
- Estimated: ~200-300 lines depending on Fourier-transform reuse.

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
- `integrable_exp_neg_mul_sq` — 1D Gaussian integrability (used in `gaussianDensity_integrable`)
- `Integrable.fintype_prod` — product of integrable functions (used in `gaussianDensity_integrable`)

## References

- Fortuin-Kasteleyn-Ginibre (1971), "Correlation inequalities"
- Holley (1974), "Remarks on the FKG inequalities"
- Preston (1974), "A generalization of the FKG inequalities"
- Pitt (1982), "Positively correlated normal variables are associated"
- Glimm-Jaffe, *Quantum Physics*, §19
