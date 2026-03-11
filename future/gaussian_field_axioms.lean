/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Future: Gaussian field axioms

These statements are NOT active axioms. They are parked here as future
proof targets. None are currently used by pphi2 or any downstream code.

## 1. `measure_unique_of_charFun` (was in GaussianField/Properties.lean)

**Statement**: If probability measure μ on `Configuration E` has characteristic
functional `∫ exp(i ω(f)) dμ = exp(-½‖Tf‖²)` for all f ∈ E, then μ = measure T.

**Proof strategy**: Lévy's continuity/uniqueness theorem for measures on
locally convex spaces, specialized to nuclear Fréchet duals.

Key steps:
1. **Finite-dimensional projections**: For each finite set of test functions
   `f₁,...,fₖ`, the pushforward `(ω(f₁),...,ω(fₖ))` is a Gaussian on ℝᵏ with
   known covariance. By the finite-dimensional Lévy theorem (in Mathlib via
   `MeasureTheory.measure_eq_of_charFun_eq`), these marginals agree.
2. **Cylinder set determination**: On nuclear spaces, the cylindrical σ-algebra
   equals the Borel σ-algebra. Two measures agreeing on all cylinder sets are
   equal. This is the same infrastructure as `future/configuration_torus.lean`.
3. **Alternatively (Minlos theorem)**: The Fourier transform on the space of
   measures over a nuclear space is injective.

**Mathlib prerequisites**:
- Finite-dimensional characteristic function uniqueness: partially available
- Cylinder set σ-algebra = Borel for nuclear spaces: NOT in Mathlib
- Minlos theorem: NOT in Mathlib

**Difficulty**: Hard. ~800-1200 LOC.

**Potential shortcut**: If `Configuration E` were a standard Borel space
(see `future/configuration_torus.lean`), then agreeing on all finite-dimensional
marginals implies equality via a π-system argument.

**References**:
- Bogachev, *Gaussian Measures*, Ch. 2
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4, Ch. IV (Minlos theorem)
- Kallenberg, *Foundations of Modern Probability*, Theorem 4.18

## 2. `not_supported_of_not_hilbertSchmidt` (was in GaussianField/Support.lean)

**Statement**: If `Σₙ ‖T(eₙ)‖² = ∞`, then a.s. `Σₙ |ω(eₙ)|² = ∞`.

**Proof strategy**: The random variables `Xₙ = ω(eₙ)` are independent Gaussians
with `E[Xₙ²] = ‖T(eₙ)‖²`. Since `Σ E[Xₙ²] = ∞` and `Xₙ²` are independent
nonneg random variables, Kolmogorov's three-series theorem (or the 0-1 law)
gives `Σ Xₙ² = ∞` a.s.

Key steps:
1. **Independence**: The `ω(eₙ)` are independent under `measure T`. This
   follows from the characteristic functional factoring over orthogonal test
   functions. Needs `ProbabilityTheory.IndepFun` formalization.
2. **Three-series theorem**: Kolmogorov's theorem: for independent RVs Xₙ,
   `Σ Xₙ` converges a.s. iff three conditions hold. Contrapositively, if
   `Σ E[Xₙ²] = ∞` (and Xₙ ≥ 0), the sum diverges.
3. **Alternative**: Use the 0-1 law. The event `{Σ Xₙ² < ∞}` is a tail event
   for independent Xₙ. Its probability is 0 or 1. Since `E[Σ Xₙ²] = ∞`,
   the probability must be 0.

**Mathlib prerequisites**:
- Kolmogorov's three-series theorem: NOT in Mathlib (main blocker)
- Kolmogorov 0-1 law: NOT in Mathlib
- Independence of `ω(eₙ)`: requires characteristic function factorization

**Difficulty**: Hard. ~500-800 LOC. Blocked on fundamental Mathlib gaps in
probability theory.

**Note**: Only needed for the converse direction of the support iff
characterization (`gaussian_support_iff`). The forward direction
(`support_of_hilbertSchmidt`: HS ⟹ a.e. summable) is fully proved.

**References**:
- Shiryaev, *Probability* (1996), Theorem III.3.1

## 3. `supportHilbertSpace_exists` (was in GaussianField/Support.lean)

**Statement**: For any positive weight sequence `w : ℕ → ℝ₊`, there exists a
separable real Hilbert space H₋ with an injective continuous embedding into
`Configuration E`, whose range is `{ω ∈ E' : Σₙ wₙ (ω(eₙ))² < ∞}`, and
whose inner product equals `⟨x,y⟩ = Σₙ wₙ x(eₙ) y(eₙ)`.

**Proof strategy**: Define `Space = {ω ∈ E' : Σₙ wₙ (ω(eₙ))² < ∞}` as a
subspace of `Configuration E`, with weighted inner product. Embedding = inclusion.

Key steps:
1. **Inner product well-defined**: For ω₁, ω₂ in the subspace, `Σ wₙ ω₁(eₙ) ω₂(eₙ)`
   converges by Cauchy-Schwarz from `Σ wₙ ωᵢ(eₙ)² < ∞`.
2. **Positive definiteness**: If `Σ wₙ ω(eₙ)² = 0` then `ω(eₙ) = 0` for all n
   (since wₙ > 0), so ω = 0 by the DM expansion axiom.
3. **Completeness**: A Cauchy sequence (ωₖ) in weighted norm has
   `ωₖ(eₙ) → cₙ` for each n, and `(cₙ) ∈ ℓ²_w`. Must show (cₙ) defines a CLF.
   Banach-Steinhaus for barrelled spaces gives equicontinuity → limit is a CLF.
4. **Separability**: Finite rational combinations of coordinate functionals
   are dense (by DM expansion).
5. **Continuity of inclusion**: The weighted ℓ² norm controls pointwise
   evaluation `|ω(eₙ)| ≤ ‖ω‖_w / √wₙ`.

**Alternative approach**: Use `ℓ²(ℕ, ℝ)` from Mathlib (`lp` at `p=2`) and
build an isometric isomorphism to the weighted subspace. This avoids custom
completion.

**Mathlib prerequisites**:
- Banach-Steinhaus for Fréchet spaces: `WithSeminorms.banach_steinhaus` —
  needs verification that it provides the right form
- `InnerProductSpace` on subtypes with `CompleteSpace` — partially available

**Difficulty**: Medium-Hard. ~300-500 LOC. Step 3 (completeness) is the crux.

**Note**: Only needed for `measure_supported_on_hilbertSpace` (showing samples
live in a weighted Sobolev space). The predicate version (`weighted_support`:
a.e. `Σₙ wₙ |ω(eₙ)|² < ∞`) is fully proved without this axiom.

**References**:
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4, §III.4
- Bogachev, *Gaussian Measures*, Ch. 3

## Dependent theorems (also removed)

- `gaussian_support_iff`: the iff bicharacterization (depends on axiom 2)
- `measure_supported_on_hilbertSpace`: samples live in H₋ (depends on axiom 3)
- `SupportHilbertSpace` structure: carrier type for axiom 3
-/

-- This file is intentionally not imported by any active module.
-- It serves as documentation for future proof targets.
