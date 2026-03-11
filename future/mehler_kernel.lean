/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Future: Mehler kernel eigenfunction expansion

This statement is NOT an active axiom. It is parked here as a future
proof target. The axiom `mehlerKernel_eq_series` remains in
`HeatKernel/PositionKernel.lean` (which is off the main build path)
and is only used by the cylinder QFT heat kernel, not by the lattice
approach used by pphi2.

## Statement

The Mehler kernel (closed-form heat kernel of H = -d²/dx² + x²) equals
its Hermite eigenfunction expansion:

  mehlerKernel t x₁ x₂ = Σₙ exp(-t(2n+1)) ψₙ(x₁) ψₙ(x₂)

where ψₙ are the L²-normalized Hermite functions.

## Proof strategies

### Approach A: Generating function identity

1. Mehler's formula is equivalent to a generating function identity for
   Hermite functions. Write both sides as power series in `r = exp(-2t)`
   and show coefficients match.
2. The Hermite functions satisfy
   `ψₙ(x) = (2ⁿ n! √π)^{-1/2} Hₙ(x) exp(-x²/2)`
   where Hₙ are the (physicists') Hermite polynomials.
3. The key identity is:
   `Σₙ rⁿ Hₙ(x) Hₙ(y) / (2ⁿ n!) = (1-r²)^{-1/2} exp(2rxy/(1+r) - r²(x²+y²)/(1-r²))`
4. Rearrange to get the Mehler kernel closed form.

This is a purely combinatorial/analytic identity, not blocked by deep
Mathlib gaps, but requires substantial special-function computation.

### Approach B: Heat equation uniqueness

1. Show the Mehler kernel satisfies the heat equation `∂K/∂t = -HK` with
   initial condition `K(0,x₁,x₂) = δ(x₁-x₂)`.
2. Show the eigenfunction expansion also satisfies the same PDE + IC.
3. By uniqueness of solutions (Widder's theorem or energy estimates), they agree.

### Mathlib prerequisites

- **Hermite polynomials**: `Mathlib.Analysis.SpecialFunctions.Polynomials.HermitePhysicist`
  exists with basic properties but NOT the generating function.
- **Hermite functions** (L² normalized): defined in this project
  (`SchwartzNuclear/HermiteFunctions.lean`) with sup bounds and
  orthonormality, but the generating function / completeness relation
  is not proved.
- **Generating function for Hermite polynomials**: NOT in Mathlib. This is
  the core mathematical identity. ~200-400 LOC to prove from scratch.
- For Approach B: heat equation uniqueness in L² is partially available
  but the position-space formulation would need work.

### Difficulty

Hard. ~400-700 LOC. The generating function identity for Hermite
polynomials is the key ingredient, not blocked by deep Mathlib gaps
but requires substantial special-function computation.

### Dependents

Used by 6 proofs in `HeatKernel/PositionKernel.lean`:
- `mehlerKernel_reproduces_hermite` — eigenfunction reproduction
- `mehlerKernel_semigroup` — semigroup property K_s * K_t = K_{s+t}
- `cylinderHeatKernel_eq_series` — cylinder kernel factorization
- Various integrability/bound lemmas

All dependents are in the cylinder QFT path, not used by pphi2.

## References

- Mehler (1866), "Ueber die Entwicklung einer Function"
- Reed-Simon, "Methods of Modern Mathematical Physics" Vol. II §X.12
- Erdélyi et al., "Higher Transcendental Functions" Vol. 2 Ch. 10
-/

-- This file is intentionally not imported by any active module.
-- It serves as documentation for future proof targets.
