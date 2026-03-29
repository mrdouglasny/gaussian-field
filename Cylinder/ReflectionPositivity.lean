/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity (OS3) for the Free Field on the Cylinder

Proves the Osterwalder-Schrader reflection positivity axiom (OS3) for the
free massive scalar field on S¹_L × ℝ:

  `G(f, Θf) ≥ 0` for all positive-time test functions f.

## Main results

- `cylinderGreen_reflection_positive` — OS3 for the free Green's function (proved)

## Mathematical background

### The Laplace transform factorization

For a test function `f = g ⊗ h` with `h` supported on `(0, ∞)` and
`Θf = g ⊗ Θh` supported on `(-∞, 0)`, the Green's function decomposes as:

  `G(f, Θf) = Σ_n |c_n(g)|² · |ĥ_L(ω_n)|² / (2ω_n)`

where:
- `c_n(g) = ⟨g, φ_n⟩_{L²(S¹)}` is the spatial Fourier coefficient
- `ĥ_L(ω) = ∫₀^∞ h(t) e^{-ωt} dt` is the Laplace transform of h
- `ω_n = resolventFreq L mass n` is the dispersion relation

Each term is a perfect square divided by a positive constant, so the
sum is non-negative. This factorization arises because the resolvent
kernel `e^{-ω|t-s|}/(2ω)` factors as `e^{-ωt} · e^{ωs}/(2ω)` when
`t > 0 > s`, turning the double integral into a product of single
integrals (Laplace transforms).

### Laplace embedding

We encode the factorization via a **Laplace embedding** CLM
`Λ : CylinderTestFunction L → ℓ²` whose components are the
Laplace-resolved spatial Fourier coefficients:

  `(Λf)_n = c_n(g) · ĥ_L(ω_n) / √(2ω_n)`

The key identity is: for positive-time f,

  `G(f, Θf) = ‖Λf‖²_{ℓ²} ≥ 0`

This makes reflection positivity a trivial consequence of the
non-negativity of norms.

### Physical significance

Reflection positivity is the Euclidean counterpart of unitarity in
quantum field theory. Via the Osterwalder-Schrader reconstruction
theorem, it implies:
- The Hilbert space of physical states has a positive-definite inner product
- The Hamiltonian is a self-adjoint operator bounded below
- Wightman positivity holds for the reconstructed Minkowski theory

## References

- Osterwalder-Schrader (1973), Axiom (A3)
- Glimm-Jaffe, *Quantum Physics*, §6.1, Theorem 6.1.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I, §3
-/

import Cylinder.GreenFunction
import Cylinder.PositiveTime

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Laplace embedding

The Laplace embedding maps test functions to ℓ² via the Laplace-resolved
spatial Fourier decomposition. For a pure tensor `g ⊗ h`:

  `(Λ(g ⊗ h))_n = c_n(g) · ĥ_L(ω_n) / √(2ω_n)`

where `ĥ_L(ω) = ∫₀^∞ h(t) e^{-ωt} dt` is the Laplace transform of h at
frequency ω, and `c_n(g)` is the n-th spatial Fourier coefficient of g.

The Laplace transform is well-defined because h ∈ 𝓢(ℝ) decays rapidly
and ω_n > 0 for mass > 0. The resulting sequence is in ℓ² because the
spatial Fourier coefficients of g ∈ C∞(S¹) decay rapidly and the Laplace
transforms are bounded. -/

/-- **The Laplace embedding** `Λ : CylinderTestFunction L → ℓ²`.

Maps test functions to ℓ² via the Laplace-resolved spatial Fourier
decomposition. The n-th component of `Λf` encodes the coupling of the
n-th spatial Fourier mode to the temporal Laplace transform at the
corresponding resolvent frequency `ω_n`.

This CLM exists because the Laplace transform `h ↦ ∫₀^∞ h(t) e^{-ωt} dt`
is bounded on 𝓢(ℝ) for each ω > 0, and the spatial Fourier coefficients
of g ∈ C∞(S¹) are rapidly decaying. -/
axiom cylinderLaplaceEmbedding (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2'

/-- **Laplace factorization identity.**

For positive-time test functions, the reflected Green's function equals
the squared ℓ²-norm of the Laplace embedding:

  `G(f, Θf) = ‖Λf‖²_{ℓ²}`

This identity encodes the Laplace transform factorization of the
resolvent kernel: for `t > 0 > s`, the kernel `e^{-ω|t-s|}/(2ω)`
factors as `e^{-ωt} · e^{ωs}/(2ω)`, making the double integral

  `∫∫ h(t) h(-s) e^{-ω|t-s|}/(2ω) dt ds = |∫₀^∞ h(t) e^{-ωt} dt|²/(2ω)`

a perfect square. Summing over spatial modes gives `‖Λf‖²`.

**Future proof target**: This can be proved by:
1. Verifying on pure tensors `g ⊗ h` using the mode decomposition
   of the mass operator and the resolvent kernel factorization
2. Extending to finite sums by bilinearity
3. Extending to the closure by continuity of both sides -/
axiom cylinderGreen_reflection_eq_laplaceNorm
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) :
    cylinderGreen L mass hmass f (cylinderTimeReflection L f) =
    @inner ℝ ell2' _ (cylinderLaplaceEmbedding L mass hmass f)
      (cylinderLaplaceEmbedding L mass hmass f)

/-! ## Reflection positivity (OS3)

The central Osterwalder-Schrader axiom: the Green's function applied
to a positive-time test function and its time reflection is non-negative.

This is an immediate consequence of the Laplace factorization identity:
`G(f, Θf) = ‖Λf‖² ≥ 0`. -/

/-- **Reflection positivity (OS3) for the free field on the cylinder.**

  `G(f, Θf) ≥ 0` for all positive-time test functions f.

This is the Euclidean counterpart of unitarity: it ensures the
reconstructed Hilbert space has a positive-definite inner product.

Proof: By the Laplace factorization identity,
  `G(f, Θf) = ‖Λf‖²_{ℓ²} ≥ 0`
since norms are non-negative. -/
theorem cylinderGreen_reflection_positive (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) :
    0 ≤ cylinderGreen L mass hmass f (cylinderTimeReflection L f) := by
  rw [cylinderGreen_reflection_eq_laplaceNorm L mass hmass f hf]
  exact real_inner_self_nonneg

/-- **Strict reflection positivity.**

  `G(f, Θf) > 0` for nonzero positive-time test functions f.

This strengthening of OS3 ensures the reconstructed Hilbert space is
non-degenerate: distinct test functions give distinct physical states.

It follows from injectivity of the Laplace embedding on positive-time
functions, which in turn follows from the Laplace transform being
injective on functions supported on (0, ∞) (a classical theorem). -/
axiom cylinderGreen_reflection_strict_positive (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) (hne : f ≠ 0) :
    0 < cylinderGreen L mass hmass f (cylinderTimeReflection L f)

end GaussianField
