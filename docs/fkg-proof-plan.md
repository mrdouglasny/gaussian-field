# FKG Axiom Proof Plan

**Date**: 2026-02-24
**Goal**: Prove or reduce the 3 FKG axioms in `Lattice/FKG.lean` to minimal
well-motivated axioms, with detailed helper lemma decomposition.

---

## Current State

### Proved
- `chebyshev_integral_inequality` — 1D FKG (base case)
- `fkg_lattice_condition_mul` — product of FKG-lattice densities is FKG-lattice
- `fkg_lattice_condition_single_site` — exp(-V) satisfies FKG when V is single-site
- `single_coord_sup_inf_sum` — v(a⊔b) + v(a⊓b) = v(a) + v(b)
- `finiteLaplacian_selfAdjoint`, `finiteLaplacian_neg_semidefinite`, `massOperator_pos_def`

### Axioms to Prove (3)
1. **`fkg_from_lattice_condition`** — FKG lattice condition ⟹ correlation inequality
2. **`gaussian_fkg_lattice_condition`** — lattice Gaussian satisfies FKG
3. **`fkg_perturbed`** — FKG for single-site perturbations of Gaussian

---

## Architecture

The key insight is the **dependency chain**:

```
                   [Axiom 2]                     [Axiom 1]
gaussian density → FKG lattice condition holds → correlation inequality
                        ↓
                   [Axiom 3]
              + single-site exp(-V) →  product density FKG → correlation ineq
```

Axiom 3 is a corollary of Axioms 1 + 2 plus the already-proved
`fkg_lattice_condition_mul` and `fkg_lattice_condition_single_site`.

The **irreducible new axiom** that may need to remain is the density bridge:
relating `latticeGaussianMeasure` (pushforward construction) to an explicit
exp(-½⟨φ,Qφ⟩) density.

---

## Axiom 1: `fkg_from_lattice_condition`

### Issue with Current Statement

The current axiom takes a density `ρ` but the measure `μ` is unrelated to `ρ`
in the signature. The standard FKG theorem requires `μ = ρ · λ` (absolutely
continuous w.r.t. a product reference measure). We need to either:

**(A)** Add a hypothesis `hμ : μ = volume.withDensity (ENNReal.ofReal ∘ ρ)`, or
**(B)** Reformulate as: for any non-negative integrable `ρ` satisfying the
lattice condition, `∫ F·G·ρ dλ · ∫ ρ dλ ≥ (∫ F·ρ dλ) · (∫ G·ρ dλ)`.

**Recommendation**: Option (B) is cleaner — state everything in terms of
weighted integrals against Lebesgue measure, avoiding `withDensity`. This
matches how Axioms 2 and 3 actually use it.

### Reformulated Statement

```
theorem fkg_from_lattice_condition {ι : Type*} [Fintype ι]
    (ρ : (ι → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lattice : FKGLatticeCondition ρ)
    (F G : (ι → ℝ) → ℝ) (hF : Monotone F) (hG : Monotone G)
    [+ integrability hypotheses for F·ρ, G·ρ, F·G·ρ, ρ w.r.t. volume] :
    (∫ φ, F φ * G φ * ρ φ) * (∫ φ, ρ φ) ≥
    (∫ φ, F φ * ρ φ) * (∫ φ, G φ * ρ φ)
```

### Proof Strategy: Induction on |ι|

**Base case** (|ι| = 1): Reduces to `chebyshev_integral_inequality` with
the weighted measure `ρ · volume`.

**Inductive step**: Pick coordinate `k ∈ ι`, split `φ = (x_k, φ_{rest})`.

### Helper Lemmas Needed

#### Lemma 1.1: `fkg_weighted_1d` (Easy)
**Statement**: For `ρ : ℝ → ℝ` with `ρ ≥ 0` and `f, g : ℝ → ℝ` monotone:
```
(∫ x, f x * g x * ρ x) * (∫ x, ρ x) ≥ (∫ x, f x * ρ x) * (∫ x, g x * ρ x)
```
**Proof**: Apply `chebyshev_integral_inequality` to the probability measure
`(1/Z) ρ · volume`, then multiply both sides by Z².

**Difficulty**: Easy — direct from `chebyshev_integral_inequality`.

#### Lemma 1.2: `fkg_lattice_condition_marginal` (Hard)
**Statement**: If `ρ : (ι → ℝ) → ℝ` satisfies `FKGLatticeCondition ρ`, and
we define the marginal by integrating out coordinate `k`:
```
ρ_marg(y) := ∫ x_k, ρ(y with k := x_k)
```
then `ρ_marg` satisfies `FKGLatticeCondition` on the reduced type `ι \ {k} → ℝ`.

**Proof sketch**: For fixed `y₁, y₂ : (ι\{k}) → ℝ`, define:
- `f(t) = ρ(y₁ ⊔ y₂ with k := t)`
- `g(t) = ρ(y₁ ⊓ y₂ with k := t)`
- `p(t) = ρ(y₁ with k := t)`
- `q(t) = ρ(y₂ with k := t)`

The FKG lattice condition on `ρ` gives `f(s)·g(t) ≥ p(min(s,t))·q(max(s,t))`
for the "right" assignments. Integrating this in `(s,t)` gives
`(∫f)(∫g) ≥ (∫p)(∫q)`, which is exactly the FKG lattice condition for `ρ_marg`.

The tricky part is the integral inequality — it uses the 1D FKG / Chebyshev
argument on carefully chosen functions.

**Difficulty**: Hard — requires Fubini on product measure + careful function
construction. This is the mathematical heart of the induction.

**Alternative**: Axiomatize this lemma directly if the proof is too involved.

#### Lemma 1.3: `monotone_condexp_weighted` (Hard)
**Statement**: If `ρ` satisfies `FKGLatticeCondition` and `F` is monotone, then
the weighted conditional expectation
```
F_avg(y) := ∫ x_k, F(y with k := x_k) * ρ(y with k := x_k)
```
is monotone in `y`.

**Proof sketch**: For `y₁ ≤ y₂`, use the FKG lattice condition to show that
the conditional density `ρ(· | y₂)` stochastically dominates `ρ(· | y₁)`, then
monotonicity of `F` gives the result.

**Difficulty**: Hard — this is Holley's criterion applied to conditional measures.

#### Lemma 1.4: `fin_equiv_split` (Medium, infrastructure)
**Statement**: For `ι` a `Fintype` with an element `k : ι`, there is a
measurable equivalence:
```
(ι → ℝ) ≃ᵐ ℝ × ((ι \ {k}) → ℝ)
```
compatible with the product σ-algebra, and Fubini applies.

**Difficulty**: Medium — need to set up the splitting and verify measurability.
Lean 4 / Mathlib has `Equiv.piEquivPiSubtypeProd` which gives
`(ι → ℝ) ≃ ((↑s) → ℝ) × ((↑sᶜ) → ℝ)` for `s : Finset ι`.

#### Lemma 1.5: `sup_inf_split_coord` (Easy, algebra)
**Statement**: For `φ, ψ : ι → ℝ`, when we split at coordinate `k`:
```
(φ ⊔ ψ) = ((φ k) ⊔ (ψ k), (φ_rest ⊔ ψ_rest))
(φ ⊓ ψ) = ((φ k) ⊓ (ψ k), (φ_rest ⊓ ψ_rest))
```
i.e., sup/inf commutes with the coordinate splitting.

**Difficulty**: Easy — from `Pi.sup_apply` / `Pi.inf_apply`.

### Recommended Approach for Axiom 1

Given the difficulty of Lemmas 1.2 and 1.3, there are two paths:

**(Path A) Full proof**: Prove all 5 helper lemmas. This requires ~500 lines
of measure theory involving Fubini, conditional measures, and careful
bookkeeping of the coordinate splitting.

**(Path B) Reduced axiomatization**: Replace the single axiom with two
more fundamental axioms:
```
axiom fkg_lattice_condition_marginal ...  -- Lemma 1.2
axiom monotone_condexp_weighted ...       -- Lemma 1.3
```
Then derive `fkg_from_lattice_condition` as a theorem via induction using
these two axioms + `chebyshev_integral_inequality`. This makes the axiom
base more transparent and each axiom more independently verifiable.

**Recommendation**: Path B — the full inductive proof is feasible but very
labor-intensive in Lean. The two replacement axioms are cleaner mathematical
statements.

---

## Axiom 2: `gaussian_fkg_lattice_condition`

### The Density Bridge Problem

The `latticeGaussianMeasure` is constructed as a pushforward of noise measure
through a series limit map. There is **no explicit density** in the current
formalization. However, the FKG lattice condition is a property of the density
`ρ(φ) = C · exp(-½⟨φ, Qφ⟩)`.

### Proposed Decomposition

#### Lemma 2.0: `latticeGaussianMeasure_density` (New Axiom — bridge)
**Statement**: The lattice Gaussian measure on `Configuration (FinLatticeField d N)`
has density proportional to `exp(-½ · ∑_{x,y} Q(x,y) · φ(x) · φ(y))` where
`Q = massOperator d N a mass` is the precision matrix.

More precisely, via the identification `Configuration (FinLatticeField d N) ≅
FinLatticeField d N` (finite-dimensional weak dual = the space itself):
```
latticeGaussianMeasure d N a mass ha hmass
  = volume.withDensity (fun φ => ENNReal.ofReal (gaussianDensity Q φ))
```
where `gaussianDensity Q φ = C · exp(-½ · ∑ x, ∑ y, Q(x,y) · φ(x) · φ(y))`.

**Difficulty**: Hard but provable (~200 lines). The chain:
1. Our `latticeGaussianMeasure` is built from `GaussianField.measure`, which
   uses `spectralCLM` and pushforward of noise measure.
2. On finite-dimensional `FinLatticeField d N`, this should equal
   `multivariateGaussian 0 (massOperator⁻¹)` from Degenne's repo (up to
   the `Configuration ≅ FinLatticeField` identification).
3. `multivariateGaussian 0 S` is `stdGaussian.map (√S · -)`.
4. `stdGaussian` = product of 1D `gaussianReal 0 1`, each with density
   `(2π)^{-1/2} exp(-x²/2)`.
5. Product density + orthonormal pushforward + linear change of variables
   (`map_linearMap_addHaar_eq_smul_addHaar`) gives explicit density.

**Alternative**: Axiomatize this single bridge and derive everything else.
This is the cleanest axiom if the 200-line proof is deferred.

**Note**: Mathlib has `gaussianReal` density, `map_linearMap_addHaar_eq_smul_addHaar`
for linear COV, and Degenne has `multivariateGaussian` + char function.
The pieces exist but aren't assembled.

#### Lemma 2.1: `quadraticForm_submodular_of_nonpos_offDiag` (Medium, key)
**Statement**: Let `Q : (ι → ℝ) → (ι → ℝ) → ℝ` be a symmetric bilinear form
represented by matrix entries `Q_{ij}`. If `Q_{ij} ≤ 0` for all `i ≠ j`, then
the quadratic form `V(φ) = ½ ∑_i ∑_j Q_{ij} φ_i φ_j` is submodular:
```
V(φ ⊔ ψ) + V(φ ⊓ ψ) ≤ V(φ) + V(ψ)
```

**Proof sketch**: Expand using `(φ⊔ψ)_i = max(φ_i, ψ_i)` and
`(φ⊓ψ)_i = min(φ_i, ψ_i)`. The diagonal terms cancel:
`φ_i² + ψ_i² = max(φ_i,ψ_i)² + min(φ_i,ψ_i)²`. For off-diagonal `i ≠ j`:
```
V(φ⊔ψ) + V(φ⊓ψ) - V(φ) - V(ψ)
  = ½ ∑_{i≠j} Q_{ij} · [max(φ_i,ψ_i)·max(φ_j,ψ_j) + min(φ_i,ψ_i)·min(φ_j,ψ_j)
                          - φ_i·φ_j - ψ_i·ψ_j]
```
The bracket `[...]` equals `|φ_i - ψ_i|·|φ_j - ψ_j|` when the ordering
is "mixed" (φ_i > ψ_i, φ_j < ψ_j or vice versa), and 0 when consistent.
Actually, more precisely:
```
max(a,b)·max(c,d) + min(a,b)·min(c,d) - a·c - b·d
```
This quantity can be computed by cases. When `a ≥ b` and `c ≥ d`:
`= a·c + b·d - a·c - b·d = 0`. When `a ≥ b` and `c < d`:
`= a·d + b·c - a·c - b·d = (a-b)(d-c) ≥ 0`. Similarly for the other cases.

So the off-diagonal contribution is `≥ 0`, and with `Q_{ij} ≤ 0` we get `≤ 0`.

**Difficulty**: Medium — pure algebra with case splits on orderings. About
100-150 lines of Lean.

#### Sub-lemma 2.1a: `max_min_product_identity` (Easy, algebra)
**Statement**: For `a, b, c, d : ℝ`:
```
max(a,b) * max(c,d) + min(a,b) * min(c,d) - a*c - b*d
  = max(0, (a-b)*(d-c))  -- or equivalently: ≥ 0 when (a-b) and (d-c) same sign
```
More usefully, the four-case version:
```
(a ⊔ b) * (c ⊔ d) + (a ⊓ b) * (c ⊓ d) ≥ a * c + b * d  -- when a≥b, c≤d
(a ⊔ b) * (c ⊔ d) + (a ⊓ b) * (c ⊓ d) = a * c + b * d  -- when orderings agree
```

**Difficulty**: Easy — `by_cases` + `sup_eq_left`/`inf_eq_right` + `ring`/`nlinarith`.

#### Lemma 2.2: `exp_neg_submodular_fkg` (Easy)
**Statement**: If `V` is submodular (`V(φ⊔ψ) + V(φ⊓ψ) ≤ V(φ) + V(ψ)`), then
`ρ(φ) = exp(-V(φ))` satisfies `FKGLatticeCondition ρ`.

**Proof**: `exp(-V(φ⊔ψ)) · exp(-V(φ⊓ψ)) = exp(-(V(φ⊔ψ)+V(φ⊓ψ)))
≥ exp(-(V(φ)+V(ψ))) = exp(-V(φ)) · exp(-V(ψ))` by monotonicity of exp.

**Difficulty**: Easy — `exp_add`, `exp_le_exp`, `neg_add`.

#### Lemma 2.3: `massOperator_nonpos_offDiag` (Easy)
**Statement**: The matrix representation of `massOperator d N a mass` has
non-positive off-diagonal entries. Specifically, for `x ≠ y : FinLatticeSites d N`:
```
⟨finLatticeDelta x, massOperator d N a mass (finLatticeDelta y)⟩ ≤ 0
```
where the inner product is the standard one on `FinLatticeField d N`.

**Proof**: The mass term `m² · I` contributes 0 for `x ≠ y`. The Laplacian term
`-Δ` has `⟨δ_x, (-Δ)(δ_y)⟩ = -a⁻² · [δ_y is neighbor of x]`. This is `≤ 0`.

**Difficulty**: Easy — direct computation from `finiteLaplacianFun` definition.

### Assembly of Axiom 2

```
latticeGaussianMeasure_density  -- (new axiom): Gaussian has density exp(-½⟨φ,Qφ⟩)
  + massOperator_nonpos_offDiag      -- (easy lemma): Q has non-positive off-diags
  + quadraticForm_submodular_of_nonpos_offDiag  -- (medium): submodularity
  + exp_neg_submodular_fkg           -- (easy): exp(-submodular) → FKG lattice cond
  → gaussian density satisfies FKGLatticeCondition

Then: density FKG + fkg_from_lattice_condition → gaussian_fkg_lattice_condition
```

**Net result**: Replace `gaussian_fkg_lattice_condition` axiom with the single
bridge axiom `latticeGaussianMeasure_density`, and derive everything else.

---

## Axiom 3: `fkg_perturbed`

### Proof Strategy

This should be a **theorem**, not an axiom, once Axioms 1 and 2 are established.

The perturbed measure `dμ_V = (1/Z) exp(-V) dμ_G` has density
`ρ_V(φ) = (1/Z) exp(-V(φ)) · ρ_G(φ)` w.r.t. Lebesgue measure. We need:

1. `ρ_G` satisfies `FKGLatticeCondition` (from Axiom 2's lemmas)
2. `exp(-V)` satisfies `FKGLatticeCondition` (proved: `fkg_lattice_condition_single_site`)
3. Product satisfies it (proved: `fkg_lattice_condition_mul`)
4. Apply `fkg_from_lattice_condition` (Axiom 1)

### Helper Lemma

#### Lemma 3.1: `fkg_from_lattice_condition_unnormalized` (Easy)
**Statement**: The unnormalized version of FKG. If `ρ ≥ 0` satisfies
`FKGLatticeCondition`, then for monotone `F, G`:
```
(∫ F·G·ρ dλ) · (∫ ρ dλ) ≥ (∫ F·ρ dλ) · (∫ G·ρ dλ)
```
This IS the reformulated Axiom 1 from above.

**Difficulty**: This is exactly the reformulated `fkg_from_lattice_condition`.

### Assembly of Axiom 3

```
fkg_lattice_condition_single_site  -- (proved): exp(-V) FKG for single-site V
  + gaussian density FKG             -- (from Axiom 2 chain)
  + fkg_lattice_condition_mul        -- (proved): product preserves FKG
  → ρ_G · exp(-V) satisfies FKGLatticeCondition
  + fkg_from_lattice_condition       -- (Axiom 1)
  → fkg_perturbed
```

---

## Summary: New Axiom Budget

### Axioms that should REMAIN axioms (irreducible)

| Axiom | Why |
|-------|-----|
| `latticeGaussianMeasure_density` | Bridge from pushforward to explicit density. Proving requires Fourier inversion on ℝⁿ. |
| `fkg_lattice_condition_marginal` | Marginal of FKG density is FKG. Hard measure theory (conditional Fubini + stochastic ordering). |
| `monotone_condexp_weighted` | Weighted conditional expectation of monotone function is monotone. Holley's criterion. |

**Total: 3 axioms** (replacing current 3, but more fundamental and independently verifiable)

### Lemmas to prove (new)

| Lemma | Difficulty | ~Lines |
|-------|-----------|--------|
| `fkg_weighted_1d` | Easy | 30 |
| `sup_inf_split_coord` | Easy | 15 |
| `max_min_product_identity` | Easy | 40 |
| `exp_neg_submodular_fkg` | Easy | 15 |
| `massOperator_nonpos_offDiag` | Easy | 40 |
| `fin_equiv_split` | Medium | 60 |
| `quadraticForm_submodular_of_nonpos_offDiag` | Medium | 120 |
| `fkg_from_lattice_condition` (induction) | Medium | 80 |

### Theorems derivable from new axioms

| Theorem | Derived from |
|---------|-------------|
| `gaussian_fkg_lattice_condition` | density axiom + submodularity + nonpos off-diag |
| `fkg_perturbed` | Axiom 1 + Axiom 2 chain + proved single-site + proved product |
| `fkg_lattice_gaussian` | trivial from `gaussian_fkg_lattice_condition` |

---

## Implementation Order

1. **Phase 1: Algebra lemmas** (no measure theory)
   - `max_min_product_identity`
   - `quadraticForm_submodular_of_nonpos_offDiag`
   - `exp_neg_submodular_fkg`
   - `massOperator_nonpos_offDiag`

2. **Phase 2: Reformulate Axiom 1**
   - Change `fkg_from_lattice_condition` to unnormalized weighted form
   - State `fkg_lattice_condition_marginal` and `monotone_condexp_weighted` as axioms
   - Prove `fkg_from_lattice_condition` by induction using these

3. **Phase 3: Prove Axiom 2**
   - State `latticeGaussianMeasure_density` axiom
   - Derive `gaussian_fkg_lattice_condition` as theorem

4. **Phase 4: Prove Axiom 3**
   - Derive `fkg_perturbed` as theorem from the chain

---

## Mathlib Tools Available

- `Measure.withDensity` — `Mathlib.MeasureTheory.Measure.WithDensity`
- `gaussianReal` with density — `Mathlib.Probability.Distributions.Gaussian.Real`
  (1D only, has `rnDeriv_gaussianReal` for density)
- `IsGaussian` — `Mathlib.Probability.Distributions.Gaussian.Basic`
  (predicate: pushforward by every continuous linear functional is 1D Gaussian)
- `HasGaussianLaw` — `Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw`
  (predicate, characteristic function based)
- `charFun` / `charFunDual` — `Mathlib.MeasureTheory.Measure.CharacteristicFunction`
  (characteristic function on inner product spaces / Banach spaces)
- `isGaussian_iff_charFun_eq` — Gaussian iff charFun = exp(i⟨t,m⟩ - C(t,t)/2)
  (in Degenne's brownian-motion repo, may be in Mathlib by now)
- `Equiv.piEquivPiSubtypeProd` — splitting `(ι → ℝ) ≃ ((↑s → ℝ) × (↑sᶜ → ℝ))`
- `Pi.sup_apply` / `Pi.inf_apply` — componentwise lattice operations
- `integral_prod` — Fubini theorem
- `Fintype.equivFin` — `ι ≃ Fin n` for induction
- `covarianceBilin` — `Mathlib.Probability.Moments.CovarianceBilin`

## External Lean Projects (potential resources)

### Brownian Motion / Gaussian Measures (Rémy Degenne) — LOCAL at `../brownian-motion`
- **Repo**: `github.com/RemyDegenne/brownian-motion`
- **Paper**: arXiv:2511.20118
- **Key file**: `BrownianMotion/Gaussian/MultivariateGaussian.lean`
- **Key definitions**:
  - `stdGaussian E` = product of 1D `gaussianReal 0 1` via orthonormal basis
  - `multivariateGaussian μ S` = pushforward of stdGaussian by `x ↦ μ + √S · x`
  - `charFun_multivariateGaussian` = `exp(⟪x,μ⟫·I - S(x,x)/2)`
  - `covarianceBilin_multivariateGaussian` = bilinear form of S
  - `covariance_eval_multivariateGaussian` = `cov[x_i, x_j] = S_{ij}`
- **Density gap**: NO `withDensity` or `rnDeriv` for multivariate Gaussians anywhere
  in the repo. The 1D `gaussianReal` has explicit density via `withDensity` in Mathlib,
  but the multivariate case only has characteristic function characterization.
- **Bridge path**: The density `C·exp(-½⟨x,Q⁻¹x⟩)` for `multivariateGaussian 0 Q⁻¹`
  could be derived via:
  1. `stdGaussian` = `(Measure.pi (fun _ => gaussianReal 0 1)).map (orthonormal basis)`
  2. Each `gaussianReal 0 1` has density `(2π)^{-1/2} exp(-x²/2)` (Mathlib)
  3. Product density = `(2π)^{-n/2} exp(-½‖x‖²)` (need `Measure.pi_withDensity` or similar)
  4. Pushforward by orthonormal map preserves volume (isometry)
  5. Pushforward by `√S` rescales by `|det(√S)|` via Mathlib's
     `map_linearMap_addHaar_eq_smul_addHaar` (EqHaar.lean:234)
  6. Change of variables gives density `(2π)^{-n/2} |det S|^{-1/2} exp(-½⟨x,S⁻¹x⟩)`
  This is a provable chain but requires ~200 lines of measure theory glue.

### LeanMillenniumPrizeProblems (Yang-Mills)
- **Repo**: `github.com/lean-dojo/LeanMillenniumPrizeProblems`
- **Key content**: `QuantumYangMillsTheory` with Wightman-style axioms,
  `OperatorValuedDistribution`, `SchwartzSpace` usage.
- **Relevance**: Minimal — uses Mathlib's `spectrum` for mass gap, doesn't
  build lattice field theory or correlation inequalities.

### PhysLean (HepLean)
- **Repo**: `github.com/HEPLean/PhysLean`
- **Key content**: Wick's theorem formalization, statistical mechanics basics.
- **Relevance**: Minimal for FKG. Wick's theorem is combinatorial (contractions),
  not related to correlation inequalities.

### physicslib4
- **Repo**: `github.com/physicslib/physicslib4`
- **Relevance**: Unknown — "Hilbert's sixth problem in Lean", limited visibility
  into contents.

### Statistical Learning Theory (YuanheZ)
- **Repo**: `github.com/YuanheZ/lean-stat-learning-theory`
- **Key content**: Gaussian Lipschitz concentration, sub-Gaussian processes.
- **Relevance**: Low — concentration inequalities are different from FKG
  correlation inequalities.

## Conclusion: No FKG Formalization Exists, but Density Bridge is Provable

As of 2026-02, **no Lean 4 formalization of the FKG inequality exists** in
Mathlib, PhysLean, or any other known project. The closest relevant
infrastructure is:

1. **Degenne's `multivariateGaussian`** (local at `../brownian-motion`):
   Provides multivariate Gaussian construction, characteristic function,
   covariance matrix identification. Missing: explicit density via `withDensity`.

2. **Mathlib's `map_linearMap_addHaar_eq_smul_addHaar`** (EqHaar.lean):
   Linear change-of-variables formula for Haar/Lebesgue measure. This is
   the key tool to go from `stdGaussian` (product of 1D densities) to
   `multivariateGaussian` (density with precision matrix).

3. **Mathlib's 1D `gaussianReal`**: Has explicit `withDensity` construction
   and `rnDeriv_gaussianReal`.

4. **Mathlib's `Pi.instLattice`**: Componentwise lattice for `FKGLatticeCondition`.

**The density bridge** (`latticeGaussianMeasure_density`, Lemma 2.0) is the
single hardest axiom to eliminate. The ingredients all exist (1D density,
linear COV, product measures) but assembling them is ~200 lines. This can
be axiomatized initially and proved later as a standalone project.

The algebraic lemmas (submodularity of quadratic forms, non-positive off-diagonal
precision) are straightforward and don't need external resources.

## References

- Fortuin-Kasteleyn-Ginibre (1971), "Correlation inequalities"
- Holley (1974), "Remarks on the FKG inequalities"
- Preston (1974), "A generalization of the FKG inequalities"
- Pitt (1982), "Positively correlated normal variables are associated"
- Glimm-Jaffe, *Quantum Physics*, §19
- Degenne et al. (2024), "Formalization of Brownian motion in Lean", arXiv:2511.20118
