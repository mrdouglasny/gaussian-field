/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Range density of the cylinder mass operator

Axiomatises the **general range-density theorem** for tensor-product mass
operators with mode-by-mode invertible per-mode operators, specialised to
the cylinder case.

## Main result

* `cylinderMassOperator_range_dense` (axiom) — `cylinderMassOperator L mass hmass`
  has dense range in `ell2'`.

## General theorem (axiomatised, in the cylinder specialisation)

Given LCTVS `E₁`, `E₂` with biorthogonal Schauder bases (`HasBiorthogonalBasis`)
and a continuous linear operator
  `T : NuclearTensorProduct E₁ E₂ →L[ℝ] lp 2`
satisfying the **mode-by-mode formula**

  `(T f)_n = DM_b (K_a (slice_a f))`    where `(a, b) := Nat.unpair n`,

if each per-mode operator `K_a : E₂ ≃L[ℝ] E₂` is a **continuous linear
equivalence** of `E₂`, then `range T` contains the standard basis
`{ e_n : n : ℕ }` of `lp 2` and is therefore dense in `lp 2`.

## Witness construction (proof of the general theorem)

For any `n = Nat.pair a₀ b₀`, the test function
  `f_n := NuclearTensorProduct.pure (basis_{a₀}) (K_{a₀}⁻¹ (basis_{b₀}))`
satisfies `T(f_n) = e_n` exactly:

* `slice_{a'} (pure (basis_{a₀}) h) = δ_{a', a₀} • h` — basis biorthogonality
  on `E₁` (`coeff_a (basis_a₀) = δ_{a, a₀}`).
* `K_{a₀} (K_{a₀}⁻¹ (basis_{b₀})) = basis_{b₀}` — `K_{a₀}` is an equivalence.
* `DM_{b'} (basis_{b₀}) = δ_{b', b₀}` — basis biorthogonality on `E₂`.

So `(T f_n)_{Nat.pair a' b'} = δ_{a', a₀} · δ_{b', b₀} = (e_n)_{Nat.pair a' b'}`,
hence `T f_n = e_n`. The standard basis `{e_n}` is dense in `lp 2`, so range T
is dense.

## Cylinder specialisation

For `cylinderMassOperator L mass hmass`:
* `E₁ := SmoothMap_Circle L ℝ`, `E₂ := SchwartzMap ℝ ℝ`.
* `K_a := resolventMultiplierCLM (resolventFreq_pos L mass hmass a)`.

`K_a` is a `ContinuousLinearEquiv` because:
1. The resolvent symbol `(p² + ω_a²)^(-1/2)` has a *temperate-growth*
   pointwise inverse `(p² + ω_a²)^(+1/2)` (degree-1 polynomial).
2. Both `M_σ` (decay symbol) and `M_{σ⁻¹}` (growth symbol) are Fourier
   multipliers on `𝓢(ℝ)` (`realFourierMultiplierCLM`).
3. Multiplier composition `M_σ ∘ M_{σ⁻¹} = M_{σ · σ⁻¹} = M_1 = id` gives
   the inverse, so `M_σ` is a `ContinuousLinearEquiv`.

## Required spectral properties

For the general theorem to apply to a mass operator `T = A^(-1/2)` over a
discrete spectral decomposition with per-mode operators `A_a` on `E₂`, the
required property is:

> Both `A_a^(+1/2)` and `A_a^(-1/2)` are topological automorphisms of `E₂`.

Equivalently, both their symbols have *temperate growth* on the relevant
spectral parameter. This holds whenever:

1. `A_a` has a strictly positive lower bound (`A_a ≥ ε > 0`) for every
   spectral mode `a` — i.e., a uniform mass gap.
2. `A_a` is a non-degenerate elliptic operator with smooth, polynomially
   bounded symbol.

For `cylinderMassOperator`, both hold via `m > 0` and the Laplacian.

## Where this would fail

* **Massless case (`m = 0`):** at the zero spatial mode, `ω_0 = 0`, so the
  symbol `|p|^(-1/2)` is singular at `p = 0`. `K_0` is not even a CLM on
  `𝓢(ℝ)`, let alone an equivalence. The mass operator's range is *not*
  dense; this is the IR divergence of massless 2D scalar field theory.
* **Higher-dim massless / tachyonic / non-elliptic cases:** the symbol fails
  to be bounded below, breaking the construction.

## References

* Reed-Simon, *Methods of Modern Mathematical Physics, Vol. II*,
  §X.12 (mass operators and resolvent multipliers).
* Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1.
-/

import Cylinder.MassOperatorConstruction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Range density of the cylinder mass operator.**

`cylinderMassOperator L mass hmass : CylinderTestFunction L → ell2'` has dense
range. This is a special case of the general range-density theorem on
tensor-product mass operators with mode-by-mode invertible per-mode operators
(see module docstring for the general statement, witness construction,
required spectral properties, and failure modes).

**Witness construction (specialised to cylinder).**
For any `n = Nat.pair a₀ b₀`, the test function

  `f_n := NuclearTensorProduct.pure
            (DyninMityaginSpace.basis a₀ : SmoothMap_Circle L ℝ)
            ((resolventMultiplierCLM (resolventFreq_pos L mass hmass a₀)).symm
              (DyninMityaginSpace.basis b₀ : SchwartzMap ℝ ℝ))`

satisfies `cylinderMassOperator L mass hmass f_n = e_n` exactly, where the
inverse `(resolventMultiplierCLM hω).symm` is the Fourier multiplier with the
temperate-growth symbol `(p² + ω²)^{1/2}`.

**Status (2026-05-10).** Axiomatised. The full discharge requires:
1. The instance `resolventMultiplier_isContinuousLinearEquiv` (the resolvent
   multiplier is a CLE on `𝓢(ℝ)`) — proves that `(p² + ω²)^{1/2}` has
   temperate growth and that multiplier composition gives the identity.
2. The general theorem on `NuclearTensorProduct` mass operators (witness +
   density of finite-supported in `lp 2`).

Both reduce to mechanical infrastructure on `realFourierMultiplierCLM` and
`NuclearTensorProduct.pure` plus standard `lp` density results. Estimated
~1–2 active days when prioritised. -/
axiom cylinderMassOperator_range_dense (mass : ℝ) (hmass : 0 < mass) :
    DenseRange (⇑(cylinderMassOperator L mass hmass) : CylinderTestFunction L → ell2')

end GaussianField

end
