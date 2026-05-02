/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite-Galerkin truncation in the harmonic-oscillator basis

API skeleton for finite-dimensional Galerkin truncation in the multi-index
Hermite-function basis on `L²(ℝ^d, dx)`, the basis Mathlib actually
provides. Built on top of the multi-index Hermite infrastructure in
`SchwartzNuclear.HermiteTensorProduct`.

## Convention (corrected 2026-05-02 after vetting)

This file uses the **Hermite-function basis** `h_α := hermiteFunctionNd d α`,
which:

* is orthonormal in `L²(ℝ^d, dx)` (Lebesgue measure, *not* Gaussian);
* consists of *Schwartz* functions (Gaussian-decay factor built in);
* diagonalises the *harmonic oscillator* `H_HO := −Δ + ‖x‖²`, with
  `H_HO h_α = (2|α| + d) h_α`, where `|α| := α.abs = ∑ᵢ αᵢ`.

This is **not** the basis natural to the Ornstein–Uhlenbeck semigroup on
`L²(ℝ^d, γ_d)` (Gaussian measure). The OU eigenbasis on `L²(γ_d)` is the
probabilists' Hermite *polynomials* `He_α / √(α!)`, and the OU generator
`L_OU = Δ − x · ∇` acts on them with eigenvalue `−|α|`. The two bases are
related by the unitary similarity transform `f ↔ e^{−‖x‖²/4} f`:

```
        L²(ℝ^d, γ_d)  ──────►  L²(ℝ^d, dx)
        He_α / √(α!)  ──────►  h_α  (up to normalising constants)
        L_OU + |α|·I  ──────►  −(H_HO − d·I)/2
```

This bridge is one-screen-of-algebra, lossless, and lets a downstream
result stated in the OU language (e.g. pphi2N's QHJ chord-action
analysis on `L²(γ_d)`) be discharged via the HO-basis API exposed here
plus the conjugation step. **The earlier version of this file claimed
`L_OU h_α = −|α| h_α` directly — that is mathematically false** (Gemini-
vetted 2026-05-02): Mathlib's `hermiteFunctionNd` is the HO basis, not
the OU basis, and stating the OU eigenvalue equation against it conflates
two different operators on two different L² spaces.

For continuity-method existence proofs (e.g., the QHJ formalism for
lattice gauge theories), one wants:

* A finite-dimensional **Galerkin truncation**: project a phase function
  onto Hermite levels of total degree `≤ d_max`. The truncation gives a
  finite system of polynomial equations on `ℝ^N`, where
  `N = #{α : MultiIndex d | α.abs ≤ d_max}`.
* A **diagonal operator with integer-spaced eigenvalues** on the truncated
  space, so that a small perturbation stays invertible by Neumann series.
  In the HO basis, that operator is `H_HO` with eigenvalue `2|α| + d`. In
  the OU basis (bridge above), it would be `L_OU` with eigenvalue `−|α|`.
  Either basis suffices: the integer-eigenvalue Newton/IFT argument is
  conjugate-invariant.
* **Implicit function theorem in finite dimensions** then gives a smooth
  (or analytic) family of solutions parameterised by `t`.

This file provides (all real definitions; two textbook-grade axioms
flag deferred discharge):

* `MultiIndex.below d_max d` — the Finset of multi-indices `α : Fin d → ℕ`
  with `α.abs ≤ d_max`. Finite and decidable.
* `hermiteGalerkinTrunc d_max f` — Galerkin projection of a Schwartz
  function `f`, defined as `∑_{α ∈ MultiIndex.below d_max d}
  hermiteCoeffNd d α f • schwartzHermiteBasisNd d α`.
* `hermiteGalerkinTrunc_tendsto_schwartz_holds` + axiom
  `hermiteGalerkinTrunc_tendsto_schwartz` — Schwartz-topology
  convergence as `d_max → ∞`. Textbook (Reed–Simon Vol. I), proof
  deferred.
* `hermiteFunctionNd_HO_eigenvalue_holds` + axiom
  `hermiteFunctionNd_HO_eigenvalue` — pointwise HO eigenvalue equation
  `(−Δ + ‖x‖²) h_α = (2|α| + d) h_α`, expressed via tensor-product
  decomposition into 1D `iteratedDeriv` factors. Textbook (separation
  of variables from Mathlib's 1D
  `hermiteFunction_harmonic_oscillator_eigenvalue`), proof deferred.
* `galerkinCoeffs d_max f` — Hermite coefficient vector,
  `fun α => hermiteCoeffNd d α.val f`.

## Status (2026-05-02, post-vetting)

**Skeleton**: definitions and statements without proofs. Discharge plan
in the bottom-of-file status note.

The previous file claimed an OU eigenvalue equation that was false at
the type level — the misclaim has been replaced with the HO eigenvalue
equation matching Mathlib's `hermiteFunction_harmonic_oscillator_eigenvalue`,
plus the OU↔HO similarity-transform bridge in the docstring above.

## References

* Bogachev, *Gaussian Measures*, AMS, 1998 — OU semigroup, Hermite basis,
  similarity transform between the two pictures.
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014 — OU generator on `L²(γ_d)` and Wick
  polynomials.
* Mathlib `hermiteFunction_harmonic_oscillator_eigenvalue` — 1D HO
  eigenvalue equation with eigenvalue `2n + 1`, the building block for
  the multi-D version stated below.
-/

import SchwartzNuclear.HermiteTensorProduct
import Mathlib.Data.Finset.Basic

noncomputable section

namespace GaussianField

open SchwartzMap

/-! ## Multi-index truncation set -/

/-- The Finset of multi-indices `α : MultiIndex d` with `α.abs ≤ d_max`.

For `d_max ∈ ℕ` and `d ∈ ℕ`, this is the set used for Galerkin
truncation: a function `f` is approximated by its Hermite expansion
restricted to total degree `≤ d_max`. The cardinality is the binomial
coefficient `C(d_max + d, d)` (stars and bars).

Construction: enumerate `Fin d → Fin (d_max + 1)` (a Fintype, since
each entry is bounded by `d_max`), map to `MultiIndex d = Fin d → ℕ`
via `Fin.val`, then filter by `α.abs ≤ d_max`.

For `d = 0` the only multi-index is the empty one (vacuously α.abs = 0
≤ d_max for any d_max). For `d_max = 0` only the zero multi-index
qualifies. -/
def MultiIndex.below (d_max : ℕ) (d : ℕ) : Finset (MultiIndex d) :=
  (Finset.univ : Finset (Fin d → Fin (d_max + 1))).image
    (fun α : Fin d → Fin (d_max + 1) => fun i : Fin d => (α i).val)
  |>.filter (fun α => α.abs ≤ d_max)

/-! ## Galerkin truncation of a Schwartz function

Given a Schwartz function `f : ℝ^d → ℝ` and `d_max : ℕ`, the
Hermite-Galerkin truncation is the finite linear combination

  P_{d_max} f = ∑_{α.abs ≤ d_max} (Hermite coeff α of f) • (Hermite basis α).

This is the orthogonal projection of `f` onto the finite-dimensional
subspace spanned by Hermite basis functions of total degree `≤ d_max`,
where orthogonality is in `L²(ℝ^d, volume)` (equivalently, in the
Gaussian-weighted L² via the standard rescaling).

The output is a Schwartz function (since it's a finite sum of Schwartz
basis functions with finite scalar weights). -/

/-- **Hermite-Galerkin truncation** at degree `d_max` in the HO basis.

  `P_{d_max} f := ∑_{α ∈ MultiIndex.below d_max d}
                    (hermiteCoeffNd d α f) • (schwartzHermiteBasisNd d α)`

Replaces an earlier `:= 0` placeholder body. The convergence
`P_{d_max} f → f` in the Schwartz topology as `d_max → ∞` is the
textbook axiom `hermiteGalerkinTrunc_tendsto_schwartz` below. -/
noncomputable def hermiteGalerkinTrunc {d : ℕ} (d_max : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  ∑ α ∈ MultiIndex.below d_max d, hermiteCoeffNd d α f • schwartzHermiteBasisNd d α

/-- **Convergence of the Galerkin truncation** in the Schwartz topology:
as `d_max → ∞`, `hermiteGalerkinTrunc d_max f → f`.

Proof: this is the Hermite expansion convergence for Schwartz functions
(`schwartzRapidDecayEquivNd`), restricted to the partial sums indexed by
`MultiIndex.below d_max d`. As `d_max → ∞`, the partial-sum index set
exhausts all of `MultiIndex d`, and the rapid-decay summability of the
Hermite coefficients gives convergence in every Schwartz seminorm.

Statement-only here; body uses `Filter.Tendsto.comp` on the existing
`schwartzRapidDecayEquivNd` plus exhaustion of partial sums. -/
def hermiteGalerkinTrunc_tendsto_schwartz_holds {d : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) : Prop :=
  Filter.Tendsto (fun d_max : ℕ => hermiteGalerkinTrunc d_max f)
    Filter.atTop (nhds f)

/-- **Textbook axiom: Schwartz-topology convergence of the Hermite-Galerkin
truncation.**

Asserts that for any Schwartz function `f : EuclideanSpace ℝ (Fin d) → ℝ`,
the multi-index Hermite expansion converges to `f` in the Schwartz
topology as the truncation degree `d_max → ∞`:

  `hermiteGalerkinTrunc d_max f → f` in `nhds f` (Schwartz seminorms).

**Proof strategy** (deferred; LOC estimate ~150–250 per Gemini).

1. The Hermite coefficient sequence `α ↦ hermiteCoeffNd d α f` of any
   Schwartz `f` is rapidly decreasing in `|α|` (proof: integration by
   parts against `hermiteFunctionNd d α`, using its `H_HO`-eigenfunction
   property to convert each Hermite operator hit into an `H_HO`
   action on `f`, plus Schwartz-seminorm bounds on `f`).
2. Rapid decay of the coefficients implies that the partial sums
   converge in every Schwartz seminorm `‖·‖_{k,ℓ}` simultaneously
   (`SchwartzMap` is a Fréchet space; the seminorm-by-seminorm bound
   follows from `iteratedFDeriv` of the partial sum being a finite
   linear combination of derivatives of basis functions, controlled
   uniformly by the rapid-decay tail). Convergence is absolute, hence
   independent of the order of summation — the result holds for *any*
   cofinal sequence of finite index sets, not just the total-degree
   truncation used here.
3. Cofinality of `MultiIndex.below d_max d` in `Finset (MultiIndex d)`
   as `d_max → ∞` gives the `atTop`-limit form.

**References.**
* Reed–Simon, *Methods of Modern Mathematical Physics, Vol. I*, §V.3
  (Hermite expansion in Schwartz space).
* Simon, *A Comprehensive Course in Analysis*.
* Bogachev, *Gaussian Measures*, AMS 1998, Thm 1.3.4.

**Status (2026-05-02)**: Postulated as textbook axiom. **Gemini-vetted
Standard**: "a fundamental theorem of analysis on Schwartz space,
stating that the Hermite functions form a topological basis
(specifically, a Schauder basis) for `𝓢(ℝ^d)`. […] The convergence is
absolute for each Schwartz semi-norm […] therefore the series converges
for *any* cofinal sequence of finite index sets, not just the specific
total-degree truncation used here." -/
axiom hermiteGalerkinTrunc_tendsto_schwartz {d : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :
    hermiteGalerkinTrunc_tendsto_schwartz_holds f

/-! ## Harmonic oscillator generator on the Hermite-function basis

Mathlib's multi-index Hermite functions `h_α := hermiteFunctionNd d α`
diagonalise the **harmonic oscillator**

  `H_HO := −Δ + ‖x‖²` on `L²(ℝ^d, dx)`,

with eigenvalue `2|α| + d`. The 1D case is Mathlib's
`hermiteFunction_harmonic_oscillator_eigenvalue`:

  `(−d²/du² + u²) hermiteFunction n = (2n + 1) · hermiteFunction n`.

The multi-D extension follows by separation of variables: each
coordinate's 1D operator contributes `2αᵢ + 1` to the eigenvalue, summing
to `2|α| + d`.

### Bridge to the OU picture

For downstream consumers stated against `L_OU = Δ − x · ∇` on `L²(γ_d)`
with eigenvalue `−|α|`: apply the unitary similarity `f ↔ e^{−‖x‖²/4} f`
to transport the HO eigenvalue equation here to the OU eigenvalue
equation. Concretely, in 1D the conjugation gives
`e^{−u²/4} L_OU e^{u²/4} = −(L̃_HO − 1/2)` where `L̃_HO := −d²/du² + u²/4`
(rescaled HO; `M⁻¹ L_OU M f = f'' + (1/2 − u²/4) f`), so `L_OU` eigenvalue
`−n` corresponds to a rescaled-HO eigenvalue `n + 1/2`, equivalently
Mathlib's `H_HO` eigenvalue `2n + 1`. The discharge of pphi2N's
`OU`-language Newton/IFT theorems goes through this conjugation; the
integer-eigenvalue Neumann perturbation argument is conjugate-invariant.

(Earlier versions of this file claimed `L_OU h_α = −|α| h_α` directly
with `h_α := hermiteFunctionNd d α`. That is **false**: `h_α` lives in
`L²(dx)`, not `L²(γ_d)`, and is an HO eigenfunction, not an OU
eigenfunction. The correction was prompted by Gemini deep-vet on
2026-05-02.) -/

/-- **HO-generator eigenvalue equation for the multi-index Hermite-function
basis** — pointwise statement, expressed via the tensor-product
decomposition `hermiteFunctionNd d α x = ∏ᵢ hermiteFunction (αᵢ) (xᵢ)`
so the multi-D Laplacian appears as a sum of 1D second derivatives:

  `−∑ᵢ (∂²/∂xᵢ²) h_α(x) + ‖x‖² h_α(x) = (2|α| + d) h_α(x)`

where `‖x‖² = ∑ᵢ xᵢ²` for `x : EuclideanSpace ℝ (Fin d)` and `Δ` is
expanded as the trace of the Hessian. The `i`-th coordinate's second
derivative acts only on the `i`-th factor of the product:

  `(∂²/∂xᵢ²) h_α(x) = (iteratedDeriv 2 (hermiteFunction (αᵢ))) (xᵢ) ·
                       ∏_{j ≠ i} hermiteFunction (αⱼ) (xⱼ).`

This Prop is the literal pointwise eigenvalue equation, expressed in
terms of Mathlib's 1D `hermiteFunction` and `iteratedDeriv` only —
intentionally avoids defining a multi-D `Δ` operator on
`EuclideanSpace ℝ (Fin d)`. The proof is separation of variables from
Mathlib's 1D `hermiteFunction_harmonic_oscillator_eigenvalue`
(eigenvalue `2n + 1`); see the axiom `hermiteFunctionNd_HO_eigenvalue`
below. -/
def hermiteFunctionNd_HO_eigenvalue_holds (d : ℕ) (α : MultiIndex d) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin d),
    (-∑ i : Fin d,
        iteratedDeriv 2 (hermiteFunction (α i)) (x i) *
          ∏ j ∈ Finset.univ.erase i, hermiteFunction (α j) (x j))
      + (∑ i : Fin d, (x i) ^ 2) * hermiteFunctionNd d α x
    = (2 * (α.abs : ℝ) + d) * hermiteFunctionNd d α x

/-- **Textbook axiom: multi-D harmonic-oscillator eigenvalue equation
for the Hermite-function basis.**

Asserts the pointwise identity `(−Δ + ‖x‖²) h_α = (2|α| + d) h_α` for
`h_α := hermiteFunctionNd d α` and `x ∈ EuclideanSpace ℝ (Fin d)`,
expanded as a sum of 1D second derivatives via the tensor-product
decomposition (see `hermiteFunctionNd_HO_eigenvalue_holds` for the
literal Lean statement).

**Proof strategy** (deferred; ~150 LOC of separation-of-variables
boilerplate). Each 1D factor satisfies Mathlib's
`hermiteFunction_harmonic_oscillator_eigenvalue`:

  `−(iteratedDeriv 2 (hermiteFunction n) y) + y² · hermiteFunction n y
   = (2n + 1) · hermiteFunction n y`.

Multiplying through by `∏_{j ≠ i} hermiteFunction (αⱼ) (xⱼ)` and
summing over `i ∈ Fin d` aggregates the eigenvalues `2αᵢ + 1` to
`Σᵢ (2αᵢ + 1) = 2|α| + d`. The `‖x‖²` term sums coordinate-wise
because `‖x‖² = Σᵢ xᵢ²` on `EuclideanSpace`.

**References.**
* Reed–Simon, *Methods of Modern Mathematical Physics, Vol. I*, §V.3
  (harmonic oscillator + separation of variables).
* Mathlib `hermiteFunction_harmonic_oscillator_eigenvalue` (1D, in
  `SchwartzNuclear/SchwartzHermiteExpansion.lean:178`).
* Bogachev, *Gaussian Measures*, AMS 1998, §1.3 (multi-index Hermite
  functions).

**Status (2026-05-02)**: Postulated as textbook axiom. **Gemini-vetted
Standard**: "the correct, canonical eigenvalue equation for the
multi-dimensional quantum harmonic oscillator on `ℝ^d`. The
multi-dimensional operator `H_d = −Δ + ‖x‖²` is separable. […] The
formulation in the `Prop` correctly captures this by applying the
second derivative to each factor in turn (as required by the Laplacian
on a product) and summing the results." All four sub-questions (Δ
expansion, eigenvalue aggregation, `‖x‖²` expression, `d = 0` edge case)
confirmed. -/
axiom hermiteFunctionNd_HO_eigenvalue (d : ℕ) (α : MultiIndex d) :
    hermiteFunctionNd_HO_eigenvalue_holds d α

/-! ## Finite-dimensional Galerkin space

For Galerkin truncation at `d_max`, the truncated function space is

  `V_{d_max} := span_ℝ { hermiteFunctionNd d α | α ∈ MultiIndex.below d_max d }`

isomorphic to `ℝ^{|MultiIndex.below d_max d|}` via the Hermite-coefficient
map. The OU generator restricted to `V_{d_max}` is a diagonal matrix on
this `ℝ^N` representation, with diagonal entries `-α.abs` for each
`α ∈ MultiIndex.below d_max d`.

This finite-dimensional setting is where the QHJ Galerkin existence
proof lives: the truncated QHJ residual is a polynomial map
`ℝ^N → ℝ^N`, and finite-dim implicit-function theorem suffices. -/

/-- **Coefficient extraction** for the Galerkin space:
`fun α => hermiteCoeffNd d α.val f` (the `L²(dx)` inner products of
`f` with the HO basis).

Replaces an earlier `fun _ => 0` placeholder that returned a zero
vector silently. -/
noncomputable def galerkinCoeffs {d : ℕ} (d_max : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :
    MultiIndex.below d_max d → ℝ :=
  fun α => hermiteCoeffNd d α.val f

/-! ## Status

Harmonic-oscillator / `L²(dx)` picture, in the type
`SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ` matching the upstream
`HermiteTensorProduct.lean` API.

Real definitions (no sorry, no axiom):

* `MultiIndex.below` — Finset of multi-indices with `α.abs ≤ d_max`.
* `hermiteGalerkinTrunc` — explicit `Finset.sum` of `hermiteCoeffNd ·
  schwartzHermiteBasisNd`.
* `galerkinCoeffs` — `fun α => hermiteCoeffNd d α.val f`.
* `hermiteGalerkinTrunc_tendsto_schwartz_holds`,
  `hermiteFunctionNd_HO_eigenvalue_holds` — Prop statements (literal
  eigenvalue equation / Tendsto in Schwartz topology).

Two textbook-grade axioms (Gemini-vetable):

* `hermiteFunctionNd_HO_eigenvalue` — multi-D HO eigenvalue equation.
  Provable from Mathlib's 1D
  `hermiteFunction_harmonic_oscillator_eigenvalue` + separation of
  variables (~150 LOC). Reed–Simon Vol. I, §V.3.
* `hermiteGalerkinTrunc_tendsto_schwartz` — Schwartz-topology
  convergence of the Hermite expansion. Provable from rapid-decay
  Hermite coefficients + Fréchet-space partial-sum control (~80 LOC).
  Reed–Simon Vol. I, §V.3.

Both axioms have detailed proof-strategy docstrings and are flagged for
discharge. They unblock the QHJ Phase B (continuity-method openness) in
`pphi2N`, which works in finite-dim Galerkin truncations and needs both
the eigenvalue equation (for invertibility of the linearisation) and
the convergence (for the `d_max → ∞` Arzelà–Ascoli step).

Pphi2N's narrative is in the OU / `L²(γ_d)` picture; the
similarity-transform bridge in the file header lets pphi2N consume the
HO statements provided here without changing its own framing. -/

end GaussianField

end
