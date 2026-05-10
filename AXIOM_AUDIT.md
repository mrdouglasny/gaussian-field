# Axiom audit — gaussian-field

*Last updated 2026-05-10.*

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

**Active axioms in build: 3.** All three are Gemini-vetted **Standard**
classical-analysis textbook results.

`scripts/count_axioms.sh` undercounts because it only scans
`{GaussianField, HeatKernel, Lattice, SchwartzNuclear}`. The full active
count is `find . -name '*.lean' -not -path './future/*' -not -path './Scratch.lean' | xargs grep -l '^axiom '`.

---

## Active axioms

### 1. `embed_l2_uniform_bound`

**File**: `Cylinder/MethodOfImages.lean:326`

**Statement** (informal): for the periodization embedding
`cylinderToTorusEmbed Ls Lt : CylinderTestFunction Ls → TorusTestFunction (Ls, Lt)`,
there exists a continuous Schwartz seminorm `q` on cylinder test functions
such that for all `Lt ≥ 1`,
`‖embed f‖²_{ℓ²} ≤ q(f)²`.

**Vetting**: **Standard** (Gemini DT-2.5, 2026-05-09). Stein-Weiss
*Fourier Analysis*, Ch. VII (Poisson summation). The hypothesis `Lt ≥ 1`
is necessary (the bound deteriorates as `Lt → 0`); uniformity matches
the textbook statement.

**Plan to fill**: Poisson summation on the temporal direction +
Riemann-sum-to-integral correction uniform in `Lt ≥ 1`. Concretely:
- For Schwartz `h : ℝ → ℝ`, the periodization has Fourier coefficients
  `(1/Lt) · 𝓕h(2πk/Lt)` on the torus.
- `‖periodize h‖²_{ℓ²(torus)} = (1/Lt²) · ∑_{k ∈ ℤ} |𝓕h(2πk/Lt)|²`,
  a Riemann sum approximation to `(1/Lt) · ‖h‖²_{L²}` (Plancherel).
- For `Lt ≥ 1`, the Riemann-sum-to-integral correction is uniformly
  bounded.

Estimate: 3-5 active days. The hardest piece is *quantitative*
Riemann-sum control uniform in the lattice spacing (Mathlib has the
qualitative Riemann sum but not the quantitative uniform bound out of
the box). DM-basis extension to general cylinder test functions adds
~1 day of bookkeeping.

No dedicated discharge plan doc yet.

### 2. `fourierMultiplier_schwartz_bound`

**File**: `SchwartzFourier/ResolventUniformBound.lean:150`

**Statement** (informal): for any smooth Fourier symbol `σ : ℝ → ℝ`
with `|D^m σ(p)| ≤ B (1+|p|)^N` for `m ≤ deriv_order`, the multiplier
`M_σ : f ↦ 𝓕⁻¹(σ · 𝓕 f)` satisfies a Schwartz-seminorm bound
`p_{k,l}(M_σ f) ≤ C' · sup_{(k',l') ∈ s} p_{k',l'}(f)`,
where `(C', s)` depends only on `(k, l, deriv_order, B, N)` — uniform
across symbol families with the same derivative bounds.

**Vetting**: **Likely correct** (Gemini DT-2.5, 2026-05-09). Stein,
*Singular Integrals*, Ch. VI (Hörmander multiplier theorem). Standard
form for continuity of `M_σ` on `𝓢(ℝ)`. The Finset-sup-of-seminorms
form is canonical; uniformity over the symbol family is correctly
captured by the quantifier order.

**Plan to fill**: Hörmander multiplier estimate on `𝓢(ℝ)` from scratch.
Substantial: the proof requires (i) Mathlib's Fourier transform on
Schwartz, (ii) seminorm propagation through pointwise multiplication,
(iii) Plancherel/Hausdorff-Young bounds for the inverse FT. Uniformity
across `σ` follows from the explicit constants in the polynomial bound.

Estimate: ~1-2 weeks. Mathlib has `SchwartzMap.fourierTransformCLM` and
`SchwartzMap.fourierMultiplierCLM` (per-symbol versions) but not
the uniform-across-symbols family bound.

No dedicated discharge plan doc yet.

### 3. `hermiteGalerkinTrunc_tendsto_schwartz`

**File**: `SchwartzNuclear/HermiteGalerkin.lean:217`

**Statement** (informal): for any Schwartz function
`f : 𝓢(ℝ^d → ℝ)`, the Hermite-Galerkin partial sum
`P_{d_max} f := ∑_{α ∈ MultiIndex.below d_max d} hermiteCoeffNd α f • schwartzHermiteBasisNd α`
converges to `f` in the Schwartz Fréchet topology as `d_max → ∞`.

**Vetting**: **Standard** (Gemini DT-2.5 2026-05-02 + DT-3.1
re-confirmation 2026-05-10). Reed-Simon Vol I §V.3, Bogachev *Gaussian
Measures* Thm 1.3.4. The Hermite functions form a topological
(Schauder) basis for `𝓢(ℝ^d)`; convergence is absolute in every
Schwartz seminorm, hence holds for any cofinal sequence of finite index
sets, not just `MultiIndex.below`.

**Plan to fill**: rapid-decay estimate on Hermite coefficients +
Schauder basis convergence in Fréchet space + cofinality of
`MultiIndex.below d_max d` in `Finset (MultiIndex d)`. Proof strategy
is recorded in the axiom's docstring (lines 185-215).

Estimate: ~1-2 weeks. Mathlib has the 1D Hermite case; the multi-D
extension via separation-of-variables + DM-basis machinery is the
substantive content. Could leverage the new
`separation_of_variables_eigenvalue` lemma for the eigenvalue
arithmetic, but the convergence proof itself is independent.

No dedicated discharge plan doc yet.

---

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
| `NuclearSpaceStd` | `future/KolmogorovGaussian.lean` | Cipollina's framework |
| `kolmogorov_gaussian_measure` | `future/KolmogorovGaussian.lean` | Kolmogorov-Minlos existence |
| `mehlerKernel_eq_series` | `future/PositionKernel.lean` | Mehler kernel series |

Plus the `future/CylinderReflectionPositivity.lean` chain (moved
2026-05-02; Lorentzian-convolution Fourier-convention bug; zero
downstream callers in active code; revival plan in the moved file's
header).

---

## Verification

- Active axiom list:
  ```
  find . -name '*.lean' -not -path './future/*' -not -path './Scratch.lean' \
    -not -name 'Test.lean' | xargs grep -lE '^axiom '
  ```
- Build clean: `lake build` succeeds (3225 jobs as of commit `4fbc467`).
