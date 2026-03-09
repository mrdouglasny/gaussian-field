# gaussian-field TODO

**6 axioms remaining (+1 skipped), 0 sorries**

## Remaining axioms — detailed analysis

### 1. `supportHilbertSpace_exists` (GaussianField/Support.lean:404)

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
   Since each ωₖ has polynomial-growth coefficients (CLF on DM space), and the
   Cauchy condition bounds them uniformly, the Banach-Steinhaus theorem for
   Fréchet spaces gives equicontinuity → the limit is again a CLF.
4. **Separability**: Finite rational combinations of "coordinate functionals"
   `eₙ* : f ↦ coeffₙ(f)` are dense (by DM expansion).
5. **Continuity of inclusion**: The weighted ℓ² norm controls pointwise evaluation
   `|ω(eₙ)| ≤ ‖ω‖_w / √wₙ`, which gives weak-* continuity.
6. **Range characterization**: `mem_range_iff` is tautological (range = subspace).

**Mathlib prerequisites**:
- Banach-Steinhaus for Fréchet spaces: `WithSeminorms.banach_steinhaus` exists
  but may need adaptation for our DM setup.
- Completion of pre-Hilbert space or direct Hilbert space construction on a
  subtype — Mathlib has `InnerProductSpace` on subtypes but not always with
  `CompleteSpace`.
- Alternatively: use `ℓ²(ℕ, ℝ)` from Mathlib (`lp` at `p=2`) and build an
  isometric isomorphism to the weighted subspace. This avoids custom completion.

**Difficulty**: Medium-Hard. ~300-500 LOC. Step 3 (completeness via
Banach-Steinhaus) is the crux.

**Subtlety**: For weights w that decay faster than any polynomial (e.g., `e^{-n}`),
elements of ℓ²_w can grow super-polynomially. Such sequences don't define CLFs
on the DM space (CLFs have polynomial-growth coefficient sequences). The
completeness argument must show the Cauchy limit stays in the polynomial-growth
regime. Banach-Steinhaus guarantees this: a pointwise-convergent sequence of
CLFs on a barrelled space (Fréchet spaces are barrelled) converges to a CLF.
Whether `WithSeminorms.banach_steinhaus` in Mathlib gives exactly this needs
checking.

---

### 2. `not_supported_of_not_hilbertSchmidt` (GaussianField/Support.lean:221)

**Statement**: If `Σₙ ‖T(eₙ)‖² = ∞`, then a.s. `Σₙ |ω(eₙ)|² = ∞`.

**Proof strategy**: The random variables `Xₙ = ω(eₙ)` are independent Gaussians
with `E[Xₙ²] = ‖T(eₙ)‖²`. Since `Σ E[Xₙ²] = ∞` and `Xₙ²` are independent
nonneg random variables, Kolmogorov's three-series theorem (or the strong law
of large numbers for independent, non-identically distributed variables) gives
`Σ Xₙ² = ∞` a.s.

Key steps:
1. **Independence**: The `ω(eₙ)` are independent under `measure T`. This
   follows from the characteristic functional: `E[exp(i Σ tₙ ω(eₙ))]` factors
   because the DM basis vectors are orthogonal in H after applying T. Need to
   formalize this as `IndepFun` in Mathlib's probability framework.
2. **Three-series theorem**: Kolmogorov's theorem says: for independent RVs Xₙ,
   `Σ Xₙ` converges a.s. iff three conditions hold. Contrapositively, if
   `Σ E[Xₙ²] = ∞` (and Xₙ ≥ 0), the sum diverges.
3. **Alternatively**: Use the 0-1 law. The event `{Σ Xₙ² < ∞}` is a tail event
   for independent Xₙ. Its probability is 0 or 1. Since `E[Σ Xₙ²] = ∞`, the
   probability must be 0.

**Mathlib prerequisites**:
- **Kolmogorov's three-series theorem**: NOT in Mathlib. This is the main blocker.
- **Independence of ω(eₙ)**: Requires `ProbabilityTheory.IndepFun` and showing
  that Gaussian pairings at orthogonal test functions are independent. May need
  characteristic function factorization.
- **Kolmogorov 0-1 law**: NOT in Mathlib (as of early 2026).
- Alternative: a direct truncation argument (truncate Xₙ² at level M, use
  `integral_tsum` for the truncated sum, Markov's inequality) could bypass
  Kolmogorov but would be complex (~400+ LOC).

**Difficulty**: Hard. ~500-800 LOC including independence + Kolmogorov or
equivalent. Blocked on fundamental Mathlib gaps in probability theory.

---

### 3. `measure_unique_of_charFun` (GaussianField/Properties.lean:217)

**Statement**: If probability measure μ on `Configuration E` has characteristic
functional `∫ exp(i ω(f)) dμ = exp(-½‖Tf‖²)` for all f ∈ E, then μ = measure T.

**Proof strategy**: This is Lévy's continuity/uniqueness theorem for measures on
locally convex spaces, specialized to nuclear Fréchet duals.

Key steps:
1. **Finite-dimensional projections**: For each finite set of test functions
   `f₁,...,fₖ`, the pushforward `(ω(f₁),...,ω(fₖ))` is a Gaussian on ℝᵏ with
   known covariance. By the finite-dimensional Lévy theorem (in Mathlib), these
   marginals agree.
2. **Cylinder set determination**: On nuclear spaces, the cylindrical σ-algebra
   equals the Borel σ-algebra. Two measures agreeing on all cylinder sets are
   equal.
3. **Alternatively (Minlos theorem)**: The Fourier transform on the space of
   measures over a nuclear space is injective. Apply to the difference μ - measure T.

**Mathlib prerequisites**:
- **Finite-dimensional characteristic function uniqueness**: Partially available
  via `MeasureTheory.measure_eq_of_charFun_eq` (for ℝⁿ, added ~2025).
- **Cylinder set σ-algebra = Borel for nuclear spaces**: NOT in Mathlib.
  This is the same gap as the `configuration_torus_borelSpace` axiom.
- **Minlos theorem**: NOT in Mathlib. Requires nuclearity + Bochner theorem
  on infinite-dimensional spaces.
- **Cramér-Wold device**: Could reduce to 1D, but still needs the cylinder
  set determination step.

**Difficulty**: Hard. ~800-1200 LOC. The fundamental blocker is the same
nuclear-space σ-algebra infrastructure needed for axioms 4-5.

**Potential shortcut**: If we could show that `Configuration E` is a standard
Borel space (via axioms 4-5), then agreeing on all finite-dimensional marginals
implies equality. This would reduce to finite-dimensional Lévy (available) +
a π-system argument. But this creates a circular dependency with axioms 4-5.

---

### 4. `configuration_torus_polish` (Torus/Restriction.lean:70)

**Statement**: `Configuration(TorusTestFunction L)` is a Polish space.

**Proof strategy**: The weak-* dual of a nuclear Fréchet space is Polish.

Key steps:
1. **Metrizability**: The weak-* topology on the dual of a nuclear Fréchet
   space is metrizable on bounded sets. Since nuclear Fréchet spaces are Montel,
   bounded = relatively compact. The full dual is a countable union of compact
   metrizable sets (Banach-Alaoglu + nuclearity gives compactness).
2. **Second-countability**: Follows from metrizability + σ-compactness.
3. **Completeness**: The dual of a Fréchet space is sequentially complete in
   the weak-* topology by Banach-Steinhaus.

**Mathlib prerequisites**:
- Nuclear Fréchet ⟹ Montel: NOT in Mathlib.
- Montel ⟹ semi-reflexive: NOT in Mathlib.
- Metrizability of weak-* on duals of nuclear Fréchet: NOT in Mathlib.
- Mathlib has `WeakDual` but very limited topology results.

**Difficulty**: Very Hard. ~800-1500 LOC of nuclear space infrastructure.

**Decision**: Keep as axiom. The mathematical justification is standard
(Schaefer III§7/IV§9, Gel'fand-Vilenkin Vol. 4 Ch. IV). The Lean
infrastructure gap is in Mathlib's nuclear space library.

---

### 5. `configuration_torus_borelSpace` (Torus/Restriction.lean:77)

**Statement**: The cylindrical σ-algebra on `Configuration(TorusTestFunction L)`
equals the Borel σ-algebra of the weak-* topology.

**Proof strategy**: On second-countable spaces, the Borel σ-algebra is generated
by open sets, and every open set is a countable union of cylinder sets (by
second-countability of the nuclear Fréchet space E).

**Mathlib prerequisites**: Same as axiom 4 (Polish ⟹ second-countable ⟹ Borel).

**Difficulty**: Very Hard (same infrastructure as axiom 4).

**Decision**: Keep as axiom. Logically coupled to axiom 4.

---

### 6. `mehlerKernel_eq_series` (HeatKernel/PositionKernel.lean:46)

**Statement**: The Mehler kernel (closed-form heat kernel of H = -d²/dx² + x²)
equals its Hermite eigenfunction expansion:
```
mehlerKernel t x₁ x₂ = Σₙ exp(-t(2n+1)) ψₙ(x₁) ψₙ(x₂)
```

**Proof strategy**: Two approaches.

**Approach A (generating function)**:
1. Mehler's formula is equivalent to a generating function identity for Hermite
   functions. Write both sides as power series in `r = exp(-2t)` and show
   coefficients match.
2. The Hermite functions satisfy `ψₙ(x) = (2ⁿ n! √π)^{-1/2} Hₙ(x) exp(-x²/2)`
   where Hₙ are Hermite polynomials.
3. The generating function identity is:
   `Σₙ rⁿ Hₙ(x) Hₙ(y) / (2ⁿ n!) = (1-r²)^{-1/2} exp(2rxy/(1+r) - r²(x²+y²)/(1-r²))`
4. Rearrange to get the Mehler kernel closed form.

**Approach B (heat equation)**:
1. Show the Mehler kernel satisfies the heat equation `∂K/∂t = -HK` with
   initial condition `K(0,x₁,x₂) = δ(x₁-x₂)`.
2. Show the eigenfunction expansion also satisfies the same PDE + IC.
3. By uniqueness of solutions (Widder's theorem or energy estimates), they agree.

**Mathlib prerequisites**:
- **Hermite polynomials**: `Mathlib.Analysis.SpecialFunctions.Polynomials.HermitePhysicist`
  exists with basic properties but NOT the generating function.
- **Hermite functions** (L² normalized): defined in this project
  (`HeatKernel/PositionKernel.lean`) but the generating function / completeness
  relation is not proved.
- **Generating function for Hermite polynomials**: NOT in Mathlib. This is the
  core mathematical identity. ~200-400 LOC to prove from scratch.
- For Approach B: heat equation uniqueness in L² is partially available but
  the position-space formulation would need work.

**Difficulty**: Hard. ~400-700 LOC. The generating function identity for Hermite
polynomials is the key ingredient, not blocked by deep Mathlib gaps but requires
substantial special-function computation.

**Note**: This axiom is only used in the cylinder QFT (harmonic oscillator heat
kernel), not in the lattice approach used by pphi2.

---

## Completed items (for reference)

### DFT / circulant diagonalization — **DONE**
All 3 target axioms proved (Lattice/CirculantDFT.lean, CirculantDFT2d.lean).

### Green's function invariance — **DONE**
Both pure-tensor axioms proved (HeatKernel/GreenInvariance.lean).

### Bilinear extension from pure tensors — **DONE**
`greenFunctionBilinear_invariant_of_pure` proved via two-step DM expansion.

### Nuclear tensor product functor — **DONE**
All 4 axioms proved (Nuclear/TensorProductFunctorAxioms.lean):
`mapCLM`, `mapCLM_pure`, `mapCLM_id`, `mapCLM_comp`.
Also: `swapCLM`, `swapCLM_pure`.

### Measure uniqueness (finite-dimensional) — partial
`measure_unique_of_charFun` could be partially proved using finite-dimensional
Lévy if the cylinder-set infrastructure (axioms 4-5) were available.

## Priority ranking

For pphi2 downstream use:
1. **Axioms 4-5** (Polish/Borel) — used in Prokhorov's theorem for continuum limit
2. **Axiom 3** (charFun uniqueness) — used in Gaussian measure construction
3. **Axiom 1** (support Hilbert space) — used in Sobolev regularity
4. **Axiom 2** (converse support) — only used for the iff characterization

Not used by pphi2:
5. **Axiom 6** (Mehler) — only for cylinder QFT
