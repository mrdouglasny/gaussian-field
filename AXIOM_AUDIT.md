# Axiom audit — gaussian-field

*Last updated 2026-10-22.*

## Purpose

In this project, an **axiom** is a *vetted provable theorem with a vetted
discharge plan* — not a fundamental unprovable assumption. Each axiom
listed below is:

1. A standard textbook fact, with explicit literature citation.
2. Reviewed for type correctness, hypothesis sufficiency, and
   non-vacuity (typically by a Gemini deep-think pass and/or a
   literature cross-check).
3. Accompanied by a concrete plan to discharge it into a Lean theorem
   (inline in the row, or linked to a dedicated discharge-plan doc).

We use the `axiom` keyword as a *staging point* — it lets the project
proceed to use a result before its full Lean proof is assembled, while
keeping the trust boundary explicit and discharge progress trackable.
The goal is for every entry below to eventually become a proved
theorem.

Format and conventions for this audit doc:
`~/.claude/AXIOM_AUDIT_FORMAT.md`.

---

**Active axioms in build: 0.**

`scripts/count_axioms.sh` undercounts because it only scans
`{GaussianField, HeatKernel, Lattice, SchwartzNuclear}`. The full active
count is `find . -name '*.lean' -not -path './future/*' -not -path './Scratch.lean' | xargs grep -l '^axiom '`.

---

## Recently discharged (2026-10-22)

All three remaining active axioms are now theorems; `#print axioms` of each shows only
`[propext, Classical.choice, Quot.sound]`.

| Former axiom | Status | Where the proof lives |
|---|---|---|
| `hermiteGalerkinTrunc_tendsto_schwartz` | Proved: unconditional Hermite expansion `schwartz_hermite_hasSum_multiIndex` (from the Hermite isomorphism) + cofinality `MultiIndex.tendsto_below`; `d = 0` by `hermiteGalerkinTrunc_dim_zero` | `SchwartzNuclear/HermiteGalerkin.lean`, `SchwartzNuclear/HermiteTensorProduct.lean` |
| `fourierMultiplier_schwartz_bound` | **False as stated** (with `deriv_order = 0`, `k = 1`: `σₙ(p) = cos(2πnp)` has `‖σₙ‖ ≤ 1` but `M_{σₙ} f = (f(·+n) + f(·−n))/2`, so `p_{1,0}(M_{σₙ} f) → ∞`). Replaced by a proved theorem in which `deriv_order` is chosen depending on `(k, l)`; `resolventSchwartz_uniformBound` (statement unchanged) now uses it | `SchwartzFourier/ResolventUniformBound.lean` (with the σ-uniform Leibniz bound `schwartz_seminorm_smulLeftCLM_le`) |
| `embed_l2_uniform_bound` | Proved: Bessel on `S¹_{Lt}` + unfolding `∫_0^{Lt} Σ_k abs (h (t + k Lt)) = ∫_ℝ abs h` give `l2InnerProduct_periodizeCLM_le` uniformly in `Lt ≥ 1`; ℓ² Minkowski over the tensor coefficients | `Cylinder/MethodOfImages.lean` (still not imported by a library root) |

---

## Recently added (2026-05-11 session)

New theorems in `WickMultivariate.lean`, all axiom-free
(`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`):

| Theorem | What it proves | Used by |
|---|---|---|
| `gffPositionCovariance` (def) | Position-space covariance kernel `C(x, y) = Σ_j γ_j(x) · γ_j(y)` | 2-site Wick formula |
| `gffPositionCovariance_symm` | Symmetry `C(x, y) = C(y, x)` | API |
| `gffPositionCovariance_self` | `C(x, x) = gffSiteVariance x` | API |
| `gff_wickPower_two_site_inner` | Janson–Hilbert 2-site Wick power formula: `∫ :φ(x)^n: :φ(y)^m: dμ_GFF = δ_{n,m} · n! · C(x, y)^n` | pphi2 `canonicalCrossTerm_inner_eq_zero` (S3 cross-term orthogonality) and `canonicalCrossTerm_l2_sq_le` (S4 per-cross-term L² bound) |

Proof uses the eigenbasis expansion (`siteWickMonomial_eigenbasis_expansion`)
+ termwise integration + `gffMultiWickMonomial_orthogonality` + a
multinomial-theorem step via Mathlib's `Finset.sum_pow_eq_sum_piAntidiag`.
Plan doc: `docs/gff-wickPower-two-site-inner-proof-plan.md`.

## Recently discharged (2026-05-10 session)

For reference. Total active axioms went **9 → 3**.

| Axiom | Discharged via | Where the proof lives |
|---|---|---|
| `cylinderMassOperator_timeReflection_norm_eq` | Parametric `id ⊗ S₂` lemma + Hermite parity | `Cylinder/MassOperatorEquivariance.lean` |
| `cylinderMassOperator_timeTranslation_norm_eq` | Parametric `id ⊗ S₂` lemma + Parseval | `Cylinder/MassOperatorEquivariance.lean` |
| `cylinderMassOperator_spatialTranslation_norm_eq` | Paired-mode rotation via `paired_coeff_product_circleTranslation` | `Cylinder/MassOperatorSpatialEquivariance.lean` |
| `cylinderMassOperator_equivariant` (master) | Wigner-style: `LinearEquiv.extend` + density + isometry upgrade | `Cylinder/GreenFunction.lean:317` (theorem block) |
| `cylinderMassOperator_range_dense` | Explicit witness construction `pure(basis_a, R⁻¹(basis_b))` + standard-basis density in `lp 2` | `Cylinder/MassOperatorRangeDense.lean` |
| `hermiteFunctionNd_HO_eigenvalue` | Generic `separation_of_variables_eigenvalue` lemma | `SchwartzNuclear/HermiteGalerkin.lean` (theorem); lemma in `GeneralResults/SeparationOfVariables.lean` |

Earlier in the session, the false structural axiom
`cylinderMassOperator_equivariant_of_heat_comm` was replaced by a safer
`CylinderSpacetimeSymmetry` structure carrying both `heat_comm` and
`preserves_T_norm` fields (the original axiom was provably wrong:
`S = 2·id` is a counterexample).

---

## Inactive / future axioms (not in active build)

| Name | File | Description |
|---|---|---|
| `schwartz_dyninMityaginSpace_axiom` | `GaussianField.lean` | Fallback (commented out); proved instance used instead. |

The Lean files `future/KolmogorovGaussian.lean` (`NuclearSpaceStd`,
`kolmogorov_gaussian_measure`), `future/PositionKernel.lean`
(`mehlerKernel_eq_series`) and `future/CylinderReflectionPositivity.lean`
(one `sorry`, Lorentzian-convolution Fourier-convention bug) were deleted
on 2026-10-22; see `TODO.md` for what each held and how to restore it from
`0a53a69`.

---

## Verification

- Active axiom list:
  ```
  find . -name '*.lean' -not -path './future/*' -not -path './Scratch.lean' \
    -not -name 'Test.lean' | xargs grep -lE '^axiom '
  ```
- Build clean: `lake build` succeeds (3225 jobs as of commit `4fbc467`).
