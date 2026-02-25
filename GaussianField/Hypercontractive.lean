/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Hypercontractive Estimate for Gaussian Measures

The fundamental estimate: for the Gaussian measure μ on E' = WeakDual ℝ E
with covariance C(f,g) = ⟨T(f), T(g)⟩_H, Wick-ordered polynomials satisfy

  ‖:ω(f)^n:‖_{L^p(μ)} ≤ (p-1)^{n/2} · ‖:ω(f)^n:‖_{L^2(μ)}

for all p ≥ 2. Equivalently, the Ornstein-Uhlenbeck semigroup P_t is a
contraction from L^2(μ) to L^p(μ) when e^{-2t} ≤ 1/(p-1).

## Proof strategy

The standard proof proceeds via the Gross log-Sobolev inequality:

1. **Log-Sobolev inequality** (Gross 1975): For the standard Gaussian measure γ
   on ℝ^n, ∫ f² log(f²/‖f‖²) dγ ≤ 2 ∫ |∇f|² dγ for all f ∈ H¹(γ).

2. **Hypercontractivity** follows from log-Sobolev by the Rothaus-Simon argument:
   d/dt ‖P_t f‖_{p(t)}^{p(t)} ≤ 0 when p'(t) = 2p(t)(p(t)-1)e^{2t}.

3. The infinite-dimensional case follows by approximation (cylindrical functions
   are dense in L^p).

## References

- L. Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975), 1061-1083
- E. Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211-227
- B. Simon, The P(φ)₂ Euclidean (Quantum) Field Theory, Ch. I
- Glimm-Jaffe, Quantum Physics, Ch. 8
-/

import GaussianField.Properties

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-! ## Nelson's hypercontractive estimate -/

/-- **Nelson's hypercontractive estimate** for the Gaussian measure.

For the centered Gaussian measure `μ = GaussianField.measure T` on
`Configuration E = WeakDual ℝ E`, the L^p norm of `ω(f)^n` is controlled
by the L^2 norm with the hypercontractive constant `(p-1)^{n/2}`:

  `(∫ |ω(f)|^{pn} dμ)^{1/p} ≤ (p-1)^{n/2} · (∫ |ω(f)|^{2n} dμ)^{1/2}`

Equivalently stated without the outer exponents:

  `∫ |ω(f)|^{pn} dμ ≤ (p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ)^{p/2}`

This is the Gaussian case. For the interacting measure (with Boltzmann
weight exp(-V)), the estimate requires additional arguments (Feynman-Kac
formula + Trotter product formula).

**Proof**: Via the Gross log-Sobolev inequality for Gaussian measures
(Gross 1975). The OU semigroup maps L² → Lᵖ contractively when
`e^{-2t} ≤ 1/(p-1)`, and Wick powers `:ω(f)^n:` are eigenfunctions
of the OU semigroup with eigenvalue `e^{-nt}`.

Reference: Gross (1975); Simon, P(φ)₂, Theorem I.17; Glimm-Jaffe Ch. 8. -/
axiom gaussian_hypercontractive
    (f : E) (n : ℕ) (p : ℝ) (hp : 2 ≤ p) :
    ∫ ω : Configuration E, |ω f| ^ (p * ↑n) ∂(measure T) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration E, |ω f| ^ (2 * ↑n) ∂(measure T)) ^ (p / 2)

/-- **Gross log-Sobolev inequality** for the Gaussian measure.

For the Gaussian measure μ and any nonneg measurable function F with
`∫ F² dμ = 1`:

  `∫ F² · log(F²) dμ ≤ 2 · ∫ |∇F|² dμ`

where ∇ is the Malliavin gradient (Fréchet derivative in the Cameron-Martin
direction). This is logically equivalent to hypercontractivity via
Rothaus's theorem.

We state a concrete corollary: for the linear observable `ω ↦ ω(f)`,
the entropy is controlled by the variance.

Reference: Gross (1975), Thm 1; Simon, P(φ)₂, Prop. I.16. -/
axiom gross_log_sobolev
    (f : E) :
    ∫ ω : Configuration E,
        (ω f) ^ 2 * Real.log ((ω f) ^ 2 /
          ∫ ω' : Configuration E, (ω' f) ^ 2 ∂(measure T))
      ∂(measure T) ≤
    2 * ‖T f‖ ^ 2

end GaussianField

end
