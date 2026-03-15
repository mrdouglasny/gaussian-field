# Plan: `PolishSpace (Configuration E)` for DyninMityaginSpace E

## Status: BLOCKED — fundamental gap identified

## The Gap

The natural approach (closed embedding of `configBasisEval` into `ℕ → ℝ`) requires showing:
if `ω_n(basis_m) → L_m` for all m (convergence on basis vectors), then `ω_n(f)` converges
for all `f ∈ E` (pointwise convergence on all of E).

**This is FALSE in general**, even for Hilbert spaces.

### Counterexample (Gemini, 2026-03-15)

Let `E = ℓ²`, `D = c₀₀` (finite sequences, dense in ℓ²).
Define `ω_n(x) = n · x_n`. Each `ω_n` is continuous.

- **Convergent on basis vectors:** For each standard basis vector `e_m`,
  `ω_n(e_m) = n · δ_{nm} → 0` as `n → ∞`. So convergent on all of `D`.
- **Unbounded elsewhere:** For `y = (n^{-3/4}) ∈ ℓ²`,
  `ω_n(y) = n^{1/4} → ∞`.

### Why the Baire argument fails

The Baire category theorem says: if `E = ⋃ V_k` with `V_k` closed, then some `V_k`
has nonempty interior. But the hypothesis requires `⋃ V_k = E`, NOT merely dense.
Convergence on basis vectors only gives `⋃ V_k ⊇ span{basis}` (dense), not `= E`.

### Why barrel theorem doesn't help

A barrel must absorb ALL of E (not just a dense subspace). The set
`V_1 = {f | ∀n, |ω_n(f)| ≤ 1}` absorbs every element of `span{basis}`,
but this does NOT make it a barrel.

## What DOES work for nuclear Fréchet spaces

The classical proof uses machinery not in Mathlib:

1. **Montel's theorem**: Bounded sets in nuclear Fréchet spaces are relatively compact.
2. **σ-compactness of the dual**: E nuclear → E is Montel → dual is σ-compact.
3. **Metrizability**: E separable → (E', weak-*) metrizable on bounded sets.
4. **Completeness**: Via Banach-Alaoglu + Montel.

References:
- Schaefer, *Topological Vector Spaces* Ch. III §7, IV §9
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 Ch. IV
- Bogachev, *Gaussian Measures* Ch. 2-3

## Current status in the codebase

The axioms `configuration_torus_polish` and `configuration_torus_borelSpace` remain
in `Torus/Restriction.lean`. The tightness theorem uses `[PolishSpace (Configuration E)]`
as a hypothesis, which is supplied by these axioms at instantiation.

## What we proved instead (2026-03-15)

- `CompleteSpace RapidDecaySeq` — sequential completeness proof
- `DyninMityaginSpace.instBaireSpace` — countable seminorms + complete → Baire
- `lowerSemicontinuous_second_moment` — Fatou for parameter-dependent integrals
- **Tightness.lean: 0 sorries** (was 2)

## Possible future approaches

### A. Prove Montel for nuclear Fréchet spaces (~800-1500 LOC)
Develop nuclear space infrastructure: Montel, semi-reflexive, metrizability of dual.
Would give PolishSpace for ALL DyninMityaginSpace, eliminating all Polish axioms.

### B. Direct proof for specific spaces (~200-400 LOC each)
For `TorusTestFunction L` or `SchwartzMap D ℝ` specifically, prove PolishSpace using
concrete properties (e.g., the Schwartz space dual is tempered distributions, which
is Polish by explicit construction).

### C. Keep axioms
The axioms are mathematically true and cause no logical issues. The tightness
theorem is fully proved modulo these well-known facts.

### D. Weaken the PolishSpace hypothesis
The tightness theorem uses PolishSpace only for `isCompact_iff_isSeqCompact` in
`coordBox_isCompact`. If we can prove compactness directly (without going through
sequential compactness in a Polish space), we can eliminate the PolishSpace hypothesis.
This might be possible using the `configBasisEval` embedding + compactness in `ℕ → ℝ`.
