/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Method of Images: Torus-to-Cylinder Green's Function Bound

Establishes the uniform bound on the asymmetric torus Green's function
`G_{Lt,Ls}(f, f)` in terms of the cylinder Green's function `G_{Ls}(f, f)`,
via the **method of images** decomposition.

## Mathematical background

The torus Green's function on `T_{Lt,Ls} = (ℝ/Lt ℤ) × S¹_{Ls}` is related
to the cylinder Green's function on `S¹_{Ls} × ℝ` by periodization in the
time direction:

  `G_{Lt,Ls}(f, f) = G_{Ls}(f, f) + Σ_{k ≠ 0} ∬ f(x) f(y) G_{Ls}(x - y + (kLt, 0)) dx dy`

The cylinder Green's function has a mass gap `m > 0`, giving exponential
decay `G_{Ls}(x) ~ e^{-m|x|}` in the temporal direction. Each wrap-around
term is therefore bounded by `C(f) · e^{-m|k|Lt}`, and the geometric
series sums to give a uniform bound.

## Main results

- `cylinderGreen_continuous_seminorm_bound` — G_{Ls}(f, f) ≤ C · q(f)²
- `torusGreen_uniform_bound` — **key result**: G_{Lt,Ls}(embed f, embed f) ≤ C · q(f)²
  uniformly in Lt ≥ 1

## Proof sketch (method of images)

The Green's function on the torus `T_{Lt,Ls}` is the periodization of the
cylinder Green's function:

  `G_{Lt,Ls}((x,t),(y,s)) = Σ_{k ∈ ℤ} G_{Ls}((x,t),(y,s + kLt))`

In the spectral representation, this is immediate: the Fourier modes on
`S¹_{Lt}` are the periodic subset of the full-line Fourier modes.

For test functions f supported on the cylinder (embedded into the torus by
periodization), the k=0 term gives the cylinder Green's function, and the
k≠0 terms are the "wrap-around" contributions from images.

Each image term involves the cylinder propagator evaluated at temporal
separation ≥ |k|Lt - diam(supp f). The mass gap gives exponential decay
`e^{-m|k|Lt}` (up to a polynomial prefactor absorbed into C(f)), so the
geometric series converges uniformly for Lt ≥ 1.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I, Ch. VIII
- Osterwalder-Schrader (1973), §3
-/

import Cylinder.GreenFunction
import Cylinder.Basic
import Torus.AsymmetricTorus
import Nuclear.GeneralMapCLM
import SchwartzNuclear.Periodization

noncomputable section

namespace GaussianField

open NuclearTensorProduct

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Embedding cylinder test functions into the asymmetric torus

A test function `f ∈ CylinderTestFunction Ls = C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)` can be
embedded into the asymmetric torus `AsymTorusTestFunction Lt Ls` by
periodizing the Schwartz (temporal) factor: `𝓢(ℝ) → C∞(S¹_{Lt})`.

For Lt large relative to the effective support of f, this periodization
preserves essentially all the information in f. -/

/-- **Periodization embedding**: embeds cylinder test functions into the
asymmetric torus by periodizing the temporal (Schwartz) direction to
period Lt.

For `f = g ⊗ h ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)`, the image is
`g ⊗ (periodize_{Lt} h) ∈ C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})`.

The periodization `periodize_{Lt} : 𝓢(ℝ) → C∞(S¹_{Lt})` sums the
translates: `(periodize_{Lt} h)(t) = Σ_{k ∈ ℤ} h(t + kLt)`. This sum
converges absolutely and uniformly (with all derivatives) because h is
Schwartz class. -/
def cylinderToTorusEmbed (Lt : ℝ) [Fact (0 < Lt)] :
    CylinderTestFunction Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  (nuclearTensorProduct_swapCLM
    (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SmoothMap_Circle Lt ℝ)).comp
  (nuclearTensorProduct_mapCLM_general
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
    (periodizeCLM Lt))

/-! ## Torus Green's function on the asymmetric torus

The continuum Green's function on the asymmetric torus `T_{Lt,Ls}` is
the spectral sum:

  `G_{Lt,Ls}(f, g) = Σ_{(n₁,n₂)} c_{n₁,n₂}(f) · c_{n₁,n₂}(g) / (μ_{n₁} + μ_{n₂} + m²)`

where `μ_{n₁}` are eigenvalues of `-Δ` on `S¹_{Lt}` and `μ_{n₂}` are
eigenvalues of `-Δ` on `S¹_{Ls}`.

This is the `greenFunctionBilinear` applied to `AsymTorusTestFunction Lt Ls`,
which already has `HasLaplacianEigenvalues` via the tensor product instance. -/

/-- The continuum Green's function on the asymmetric torus `T_{Lt,Ls}`.

This is `greenFunctionBilinear` applied to the tensor product of circle
spaces with periods Lt and Ls. The eigenvalues are sums
`(2πn₁/Lt)² + (2πn₂/Ls)²` from the tensor product instance. -/
def asymTorusContinuumGreen (Lt : ℝ) [Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) : ℝ :=
  greenFunctionBilinear mass hmass f g

/-! ## Cylinder Green's function: continuous seminorm bound

The cylinder Green's function `G_{Ls}(f, f)` is bounded by a continuous
seminorm of f. This follows from continuity of the mass operator
`T : CylinderTestFunction Ls → ℓ²` and the Cauchy-Schwarz inequality. -/

/-- **The cylinder Green's function is bounded by a continuous seminorm.**

There exists a continuous seminorm `q` on `CylinderTestFunction Ls` such that

  `G_{Ls}(f, f) ≤ q(f) ^ 2`

for all test functions f.

**Proof sketch**: Since `G_{Ls}(f, f) = ‖T f‖²_{ℓ²}` where
`T : CylinderTestFunction Ls →L[ℝ] ℓ²` is the continuous mass operator,
we have `G_{Ls}(f, f) = ‖T f‖² ≤ ‖T‖² · ‖f‖²`. More precisely, since
`CylinderTestFunction Ls` is a nuclear Fréchet space (not normed), the
continuity of T means there exists a continuous seminorm p with
`‖Tf‖ ≤ p(f)`, giving `G_{Ls}(f, f) ≤ p(f)²`. -/
axiom cylinderGreen_continuous_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ f : CylinderTestFunction Ls,
        cylinderGreen Ls mass hmass f f ≤ q f ^ 2

/-! ## Uniform bound: the main result for Route B' IR limit

Combining the method of images decomposition with the exponential
suppression of wrap-around terms gives a uniform bound on the torus
Green's function, valid for all Lt ≥ 1. -/

/-- **Uniform bound on the torus Green's function (Route B' IR limit).**

There exists a continuous seminorm `q` on `CylinderTestFunction Ls` and
a constant `C > 0` such that

  `G_{Lt,Ls}(embed f, embed f) ≤ C · q(f) ^ 2`

for all `f : CylinderTestFunction Ls` and all `Lt ≥ 1`.

This is the key estimate for the IR limit `Lt → ∞` in Route B': it shows
that the torus two-point function is uniformly bounded (in Lt) by a
continuous seminorm of the cylinder test function. Together with the
Nelson-Symanzik convergence `G_{Lt,Ls} → G_{Ls}` as `Lt → ∞`, this
gives the existence of the thermodynamic limit.

**Proof sketch** (method of images):
1. Decompose: `G_{Lt,Ls}(embed f, embed f) = G_{Ls}(f, f) + wrapAround(Lt, f)`
   where the wrap-around sums over periodic images `k ≠ 0`.
2. By `cylinderGreen_continuous_seminorm_bound`: `G_{Ls}(f, f) ≤ q(f)²`.
3. Each image at distance `|k|Lt` contributes `≤ q'(f)² · e^{-m|k|Lt}`,
   so `|wrapAround| ≤ q'(f)² · 2e^{-mLt}/(1 - e^{-mLt})`.
4. For `Lt ≥ 1`, bound the geometric factor by `2e^{-m}/(1 - e^{-m})`.
5. Combining: `G_{Lt,Ls}(embed f, embed f) ≤ (1 + K) · (q+q')(f)²`. -/
axiom torusGreen_uniform_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f : CylinderTestFunction Ls,
          asymTorusContinuumGreen Ls Lt mass hmass
            (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
          C * q f ^ 2

end GaussianField
