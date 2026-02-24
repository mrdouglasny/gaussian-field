# External Axiom Review Results

**Date**: 2026-02-23
**Method**: Axioms sent in 5 thematic groups for independent mathematical review.
**Sources**: Web search for standard references, cross-checked against Glimm-Jaffe, Simon, Reed-Simon, Osterwalder-Schrader.

---

## Group 1: Heat Kernel Axioms (gaussian-field)

**File**: `HeatKernel/PositionKernel.lean`

### mehlerKernel_eq_series
- **Verdict**: CORRECT
- **Convention**: Uses H = -d²/dx² + x² (no factor of 1/2), eigenvalues λ_k = 2k+1. Internally consistent.
- **References**: Mehler (1866), Reed-Simon Vol II §X.12, Folland "Harmonic Analysis in Phase Space"
- **Proof strategy**: Substitute ρ = exp(-2t) into Mehler generating function identity, or show closed-form kernel satisfies same PDE with same initial condition.

### mehlerKernel_pos
- **Verdict**: CORRECT — **should be a theorem, not axiom**
- **Proof**: Direct from closed form: (2πsinh 2t)^{-1/2} > 0 and exp(...) > 0. Straightforward `positivity`-style proof.

### mehlerKernel_reproduces_hermite
- **Verdict**: CORRECT
- **Proof strategy**: Substitute series expansion, exchange sum/integral (absolute convergence), apply orthonormality of Hermite functions.

### mehlerKernel_semigroup
- **Verdict**: CORRECT (Chapman-Kolmogorov equation)
- **Proof strategy**: Series expansion + Fubini + orthonormality → collapse double sum → combine exponentials.

### circleHeatKernel_pos
- **Verdict**: CORRECT but proof is non-trivial
- **Proof strategy**: Must use Poisson summation (periodized Gaussian representation), NOT term-by-term positivity of Fourier series. Each Gaussian summand is positive.

### All other heat kernel axioms (summability, symmetry, periodicity, semigroup, reproducing)
- **Verdict**: All CORRECT, standard heat kernel theory.

### Recommendation
- Promote `mehlerKernel_pos` from axiom to theorem (easy proof from closed form).

---

## Group 2: FKG Inequality and Lattice Structure

### fkg_from_lattice_condition
- **Verdict**: CORRECT (Fortuin-Kasteleyn-Ginibre 1971, Holley 1974)
- **The FKG lattice condition** (log-supermodularity): ρ(x∨y)·ρ(x∧y) ≥ ρ(x)·ρ(y)
- **Proof strategy**: Holley's coupling proof via monotone Markov chain, or induction on |Λ| integrating out one coordinate at a time.
- **References**: Preston (1974) "A Generalization of the FKG Inequalities", Holley (1974)

### gaussian_fkg_lattice_condition
- **Verdict**: CORRECT
- **Key fact**: Precision matrix Q = -Δ + m² has non-positive off-diagonal entries (Q_{xy} = -1 for neighbors), which implies log-supermodularity of the Gaussian density exp(-½⟨φ,Qφ⟩).
- **References**: Pitt (1982) "Positively correlated normal variables are associated"

### fkg_perturbed — FIXED
- **Verdict**: CORRECT (after fix)
- **Key insight**: Convexity of V is NOT needed. For single-site V(φ) = Σ_x v(φ(x)), the weight exp(-V) = Π_x exp(-v(φ(x))) is a product of single-variable functions, which is automatically log-supermodular. Product of log-supermodular functions is log-supermodular.
- **Fix applied** (2026-02-23): Hypothesis weakened from `hV_convex : ConvexOn ℝ Set.univ V` to `hV_single_site` with single-site decomposition.

### ~~latticeInteraction_convex~~ — FALSE → FIXED
- **Verdict**: **Was FALSE** — now removed and replaced.
- **Why it was false**: For P(τ) = τ⁴/4 - μτ² (φ⁴ with negative mass), P''(τ) = 3τ² - 2μ < 0 near τ=0. So P is NOT globally convex. V = Σ P(φ(x)) is NOT convex.
- **Fix applied** (2026-02-23): Axiom removed entirely. Replaced with proved theorem `latticeInteraction_single_site` (V decomposes as sum of single-site functions). Upstream `fkg_perturbed` updated to take `hV_single_site` instead of `hV_convex`.
- **References**: Ellis-Monroe-Newman (1976), Simon *P(φ)₂ Euclidean QFT*

### latticeEnum_norm_bound
- **Verdict**: CORRECT
- **Key fact**: #{x ∈ ℤ^d : ‖x‖₁ ≤ R} = Θ(R^d), so shell enumeration gives ‖enum⁻¹(m)‖₁ ≤ C·(1+m)^{1/d}.
- **Proof strategy**: Shell enumeration by ℓ¹ norm + volume counting.

---

## Group 3: Transfer Matrix and Spectral Gap

### transferEigenvalue_pos
- **Verdict**: CORRECT
- **Proof**: T has strictly positive kernel → positivity-improving → no zero eigenvalue. Combined with positive-definiteness gives all eigenvalues > 0.
- **References**: Reed-Simon Vol IV §XIII.12

### transferEigenvalue_antitone
- **Verdict**: CORRECT (enumeration convention)
- **Essentially definitional**: eigenvalues listed in decreasing order via min-max principle.

### transferEigenvalue_ground_simple (Perron-Frobenius)
- **Verdict**: CORRECT
- **Perron-Frobenius is applicable**: T = exp(-aH) has strictly positive continuous kernel on L²(ℝ^{N_s}), making it positivity-improving. The infinite-dimensional Perron-Frobenius theorem (Reed-Simon IV, Theorem XIII.44) gives simplicity of the leading eigenvalue.
- **References**: Reed-Simon Vol IV Thm XIII.44, Simon "Functional Integration and Quantum Physics"

### spectral_gap_uniform
- **Verdict**: CORRECT — this is the central result of Glimm-Jaffe
- **Statement form**: ∃ m₀ > 0, ∃ a₀ > 0, ∀ a ≤ a₀, massGap ≥ m₀. This correctly captures the uniform mass gap bound needed for the continuum limit.
- **Proof difficulty**: VERY HARD — requires Glimm-Jaffe-Spencer cluster expansion techniques.
- **References**: Glimm-Jaffe-Spencer (1974), Glimm-Jaffe *Quantum Physics* §19.3

### spectral_gap_lower_bound
- **Verdict**: CORRECT with caveat
- **Caveat**: Linear-in-mass bound (gap ≥ c·mass) is correct for weak coupling and free field. For strong coupling the relationship is more complex, but the existential hides the coupling dependence acceptably.
- **References**: "On the Glimm-Jaffe linear lower bound in P(φ)₂" (1972)

---

## Group 4: OS Axioms and Continuum Limit

### os0_inheritance
- **Verdict**: TRUE but TOO WEAK
- **Issue**: States all moments are finite, but the actual OS0 requires factorial growth bound: |S_n(f₁,...,f_n)| ≤ C^n · n! · Π‖f_i‖_s. Mere integrability is necessary but not sufficient for OS reconstruction.
- **Recommendation**: Strengthen to include the E0' linear growth condition.

### ⚠️ os1_inheritance — VACUOUS
- **Verdict**: **TRIVIALLY TRUE for ALL probability measures** — does not capture OS1
- **Issue**: |∫ cos(ω(f)) dμ| ≤ 1 holds by |cos| ≤ 1 + triangle inequality. The actual OS1 (regularity) requires |Z[f]| ≤ exp(c·‖f‖²_{H⁻¹}).
- **Recommendation**: Replace with actual Sobolev growth bound.

### rp_closed_under_weak_limit (THEOREM, not axiom)
- **Verdict**: CORRECT, genuinely proved
- **The proof is clean**: bounded continuous test function → weak convergence of integrals → limit of nonneg sequence is nonneg.
- **References**: Glimm-Jaffe §19.4, Jaffe "Reflection Positivity Then and Now" (arXiv:1802.07880)

### continuumMeasures_tight
- **Verdict**: CORRECT
- **Proof route**: Mitoma's criterion reduces tightness on S'(ℝ²) to one-dimensional projections → uniform second moment bounds → Chebyshev.
- **References**: Mitoma (1983), Simon *P(φ)₂* §V.1

### second_moment_uniform
- **Verdict**: CORRECT
- **Key bound**: ∫|ω(f)|² dμ_a ≤ e^{C|Λ|} · ⟨f, G_a f⟩ where G_a → G as a→0, giving uniform bound.

### ⚠️ moment_equicontinuity — WRONG AS STATED
- **Verdict**: **MATHEMATICALLY INCORRECT**
- **Issue**: The RHS is a bare constant C, but the bound MUST depend on ‖f-g‖ in a Sobolev/Schwartz norm. Taking f = n·h, g = 0 gives moment ~ n² which defeats any fixed C.
- **Correct formulation**: ∫|ω(f-g)|² dμ_a ≤ C · ‖f-g‖²_s for some Schwartz seminorm of order s.
- **Fix**: Multiply RHS by `schwartz_seminorm_sq s (f - g)`.

---

## Group 5: Wick Ordering, Ward Identity, Reflection Positivity

### wickMonomial_eq_hermite
- **Verdict**: CORRECT
- **Convention**: Uses probabilist's Hermite He_n (Mathlib's `Polynomial.hermite`). Formula :x^n:_c = c^{n/2} · He_n(x/√c) is standard.
- **Verified by checking** n=2,3,4 against proved `wickMonomial_two/three/four`.
- **Proof strategy**: Induction on n using Hermite recursion He_{n+1}(t) = t·He_n(t) - n·He_{n-1}(t) transformed via scaling.
- **References**: Simon *P(φ)₂* §I.3, Glimm-Jaffe §8.6

### wickPolynomial_bounded_below
- **Verdict**: CORRECT
- **Key fact**: Leading term (1/n)x^n dominates lower-order Wick corrections. Even degree + positive leading coefficient → bounded below.
- **Proof strategy**: Split into |x| ≥ R (leading term dominates) and |x| ≤ R (EVT on compact set). Straightforward real analysis.
- **References**: Nelson (1966), Simon §I

### wickConstant_log_divergence
- **Verdict**: CORRECT
- **Convention**: Factor (2π)⁻¹ is correct for d=2 (from ∫d²k/(k²+m²) in momentum space with UV cutoff at π/a).
- **Proof strategy**: HARD — requires Euler-Maclaurin approximation of lattice sum by integral + explicit integral evaluation in polar coordinates.
- **References**: Simon §I.4, Glimm-Jaffe §8.6

### action_decomposition
- **Verdict**: CORRECT in structure
- **Key**: S[φ] = S₊[φ₊,φ₀] + S₊[Θφ₋,φ₀] — nearest-neighbor coupling means action splits at reflection plane.
- **Minor issue**: `sorry` in type signature for NeZero proof (bookkeeping, not mathematical).
- **References**: Osterwalder-Seiler (1978), Fröhlich-Israel-Lieb-Simon (1978)

### ward_identity_lattice + scaling dimension argument
- **Verdict**: CORRECT
- **Super-renormalizability argument is valid**: Lattice Laplacian correction has dim=4 > d=2, giving O(a²) anomaly. In P(φ)₂, super-renormalizability means no log corrections (all Feynman diagrams finite after Wick ordering).
- **References**: Symanzik (1983) "Continuum limit and improved action", Huebner et al. (2012) arXiv:1204.4146

---

## Critical Issues Summary

### Must Fix (mathematical errors)

1. ~~**`latticeInteraction_convex`**~~ — **FIXED** (2026-02-23). Removed and replaced with proved `latticeInteraction_single_site`. Upstream `fkg_perturbed` also updated.

2. **`moment_equicontinuity`** (Tightness.lean:89) — **WRONG as stated**. RHS must depend on ‖f-g‖_s, not be a bare constant.

### Should Fix (too weak to be useful)

3. **`os1_inheritance`** (AxiomInheritance.lean:100) — **VACUOUS**. Replace with actual Sobolev growth bound |Z[f]| ≤ exp(c·‖f‖²).

4. **`os0_inheritance`** (AxiomInheritance.lean:77) — **TOO WEAK**. Strengthen to include factorial growth bound (E0' condition).

### Optimization Opportunities

5. **`mehlerKernel_pos`** — Should be theorem, not axiom (trivial from closed form).

6. ~~**`fkg_perturbed`**~~ — **FIXED** (2026-02-23). Hypothesis weakened from convexity to single-site decomposition.

### Placeholder Axioms (23 with conclusion `True`)

These are structurally harmless but provide no mathematical content. Priority for strengthening:
- Transfer matrix properties (selfAdjoint, positiveDefinite, traceClass, hilbertSchmidt)
- Ward identity + scaling dimension
- Lattice RP
- Schwinger function convergence

---

## Proof Strategy Recommendations

### Provable now (within Mathlib capabilities)
1. `mehlerKernel_pos` — positivity from closed form
2. `wickPolynomial_bounded_below` — real analysis (EVT + polynomial asymptotics)
3. `transferEigenvalue_antitone` — definitional from enumeration

### Provable with moderate effort
4. `wickMonomial_eq_hermite` — induction + Hermite recursion algebra
5. `mehlerKernel_reproduces_hermite` — series expansion + orthonormality
6. `mehlerKernel_semigroup` — series expansion + Fubini + orthonormality

### Hard (deep analytic content)
7. `mehlerKernel_eq_series` — Mehler's formula (PDE uniqueness or generating function)
8. `circleHeatKernel_pos` — requires Poisson summation
9. `wickConstant_log_divergence` — Euler-Maclaurin + explicit integral
10. `spectral_gap_uniform` — Glimm-Jaffe-Spencer cluster expansion

---

## References

- Fortuin, Kasteleyn, Ginibre, "Correlation inequalities on some partially ordered sets" (1971)
- Preston, "A Generalization of the FKG Inequalities" (1974)
- Holley, "Remarks on the FKG inequalities" (1974)
- Ellis, Monroe, Newman, "The GHS and other correlation inequalities for a class of even ferromagnets" (1976)
- Pitt, "Positively correlated normal variables are associated" (1982)
- Osterwalder-Schrader, "Axioms for Euclidean Green's Functions II" (1975)
- Glimm-Jaffe-Spencer, "The Wightman axioms and particle structure in the P(φ)₂ quantum field model" (1974)
- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974)
- Reed-Simon, *Methods of Modern Mathematical Physics* Vol II, IV
- Jaffe, "Reflection Positivity Then and Now" (arXiv:1802.07880)
- Mitoma, "Tightness of Probabilities on C([0,1]; S') and D([0,1]; S')" (1983)
- Symanzik, "Continuum limit and improved action in lattice theories" (1983)
- Huebner et al., "Restoration of Rotational Symmetry in the Continuum Limit" (arXiv:1204.4146)
- Mehler, "Ueber die Entwicklung einer Function von beliebig vielen Variablen" (1866)
