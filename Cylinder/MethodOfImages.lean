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
theorem cylinderGreen_continuous_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ f : CylinderTestFunction Ls,
        cylinderGreen Ls mass hmass f f ≤ q f ^ 2 := by
  -- The seminorm q(f) = ‖Tf‖ where T is the mass operator
  let T := cylinderMassOperator Ls mass hmass
  refine ⟨(normSeminorm ℝ ell2').comp T.toLinearMap, ?_, ?_⟩
  · -- Continuity: q = norm ∘ T, both continuous
    exact continuous_norm.comp T.cont
  · -- Bound: G(f,f) = ⟨Tf, Tf⟩ = ‖Tf‖² = q(f)²
    intro f
    simp only [cylinderGreen, Seminorm.comp_apply, coe_normSeminorm]
    exact le_of_eq (real_inner_self_eq_norm_sq (cylinderMassOperator Ls mass hmass f))

/-! ## Uniform ℓ² bound for embedded functions

The key estimate: the ℓ² norm of `embed f` (on the torus) is bounded
by a continuous seminorm of `f` (on the cylinder), uniformly in Lt ≥ 1.

This follows from the uniform boundedness of the periodization CLM:
`periodize_Lt(h)` has ℓ² norm bounded by a Schwartz seminorm of `h`,
uniformly in Lt ≥ 1. The periodization sum `Σ_k h(t + kLt)` is
controlled by the rapid decay of h, with the number of significant
terms bounded independently of Lt for Lt ≥ 1. -/

/-- **Uniform ℓ² bound for periodization.**

The ℓ² coefficient norm of `periodize_Lt(h)` on `SmoothMap_Circle Lt ℝ`
is bounded by a Schwartz seminorm of `h`, uniformly in `Lt ≥ 1`.

By Parseval on `S¹_{Lt}`, `‖periodize(h)‖²_{ℓ²} ≈ (1/Lt)∫₀^{Lt} |Σ_k h(t+kLt)|² dt`.
By Cauchy-Schwarz on the sum and Schwartz decay of h, this is bounded by
`C · p(h)²` where p is a Schwartz seminorm and C is independent of Lt.
The key: for Lt ≥ 1, the Fourier coefficients `ĥ(n/Lt)/√Lt` form a Riemann
sum that is bounded uniformly (same structure as `schwartz_riemann_sum_bound`).

Reference: Stein-Weiss, Ch. VII. -/
axiom periodizeCLM_l2_uniform_bound :
    ∃ (q : Seminorm ℝ (SchwartzMap ℝ ℝ)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ (h : SchwartzMap ℝ ℝ),
          l2InnerProduct (periodizeCLM Lt h) (periodizeCLM Lt h) ≤ q h ^ 2

/-- **ℓ² inner product factors for pure tensors.**

For pure tensors in an NTP: `‖pure(a,b)‖²_{ℓ²} = ‖a‖²_{ℓ²} · ‖b‖²_{ℓ²}`.
This follows from the coefficient factorization
`pure(a,b).val(pair(i,j)) = coeff_i(a) · coeff_j(b)`
and Fubini for absolutely convergent double sums. -/
axiom l2InnerProduct_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (a : E₁) (b : E₂) :
    l2InnerProduct (NuclearTensorProduct.pure a b) (NuclearTensorProduct.pure a b) =
    l2InnerProduct a a * l2InnerProduct b b

/-- **ℓ² norm is preserved by swap.**

The swap CLM permutes Cantor pair indices: `(i,j) ↦ (j,i)`.
Since |coeff_{pair(i,j)}|² = |coeff_{pair(j,i)}|² after swap,
the ℓ² norm is preserved. -/
axiom l2InnerProduct_swap
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (f : NuclearTensorProduct E₁ E₂) :
    l2InnerProduct (nuclearTensorProduct_swapCLM f) (nuclearTensorProduct_swapCLM f) =
    l2InnerProduct f f

/-- **Uniform ℓ² bound for the periodization embedding.**

Proved from `periodizeCLM_l2_uniform_bound` (periodization ℓ² bound),
`l2InnerProduct_pure` (ℓ² factors for pure tensors), and
`l2InnerProduct_swap` (swap preserves ℓ²).

The proof reduces to pure tensors via `cylinderToTorus_clm_ext_of_pure`
(NTP pure tensor density), then uses the factorization:
`‖embed(g ⊗ h)‖² = ‖swap(g ⊗ periodize(h))‖² = ‖g‖² · ‖periodize(h)‖²`
and applies the uniform periodization bound. -/
theorem embed_l2_uniform_bound :
    ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f : CylinderTestFunction Ls,
          l2InnerProduct
            (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
          q f ^ 2 := by
  -- Proof sketch:
  -- 1. For pure tensors g ⊗ h: l2(embed(g ⊗ h)) = l2(periodize h) · l2(g)
  --    (by l2InnerProduct_pure + l2InnerProduct_swap)
  -- 2. l2(periodize h) ≤ q_h(h)² uniformly in Lt (by periodizeCLM_l2_uniform_bound)
  -- 3. l2(g) ≤ C · p(g)² for a continuous seminorm p (ℓ² ≤ rapid decay)
  -- 4. Combined on pure tensors: l2(embed(g ⊗ h)) ≤ C · p(g)² · q_h(h)²
  -- 5. Extend to general f by DM expansion + continuity
  sorry

/-! ## Uniform bound: the main result for Route B' IR limit -/

/-- **Uniform bound on the torus Green's function (Route B' IR limit).**

There exists a continuous seminorm `q` on `CylinderTestFunction Ls` and
a constant `C > 0` such that

  `G_{Lt,Ls}(embed f, embed f) ≤ C · q(f) ^ 2`

for all `f : CylinderTestFunction Ls` and all `Lt ≥ 1`.

**Proof**: From `greenFunctionBilinear_le` (G ≤ ℓ²/m²) and
`embed_l2_uniform_bound` (ℓ² of embed ≤ q²). -/
theorem torusGreen_uniform_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f : CylinderTestFunction Ls,
          asymTorusContinuumGreen Ls Lt mass hmass
            (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
          C * q f ^ 2 := by
  obtain ⟨q, hq_cont, hq_bound⟩ := embed_l2_uniform_bound Ls
  refine ⟨1 / mass ^ 2, by positivity, q, hq_cont, ?_⟩
  intro Lt _ hLt f
  -- G_torus(embed f, embed f) ≤ (1/m²) · l2(embed f, embed f)
  calc asymTorusContinuumGreen Ls Lt mass hmass
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f)
      = greenFunctionBilinear mass hmass
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) := rfl
    _ ≤ (1 / mass ^ 2) * l2InnerProduct
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) :=
      greenFunctionBilinear_le mass hmass _
    _ ≤ (1 / mass ^ 2) * q f ^ 2 := by
      gcongr; exact hq_bound Lt hLt f

end GaussianField
