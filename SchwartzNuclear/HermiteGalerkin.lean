/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite-Galerkin truncation and the OU semigroup generator

API skeleton for finite-dimensional Galerkin truncation in the multi-index
Hermite basis, plus the OU (Ornstein-Uhlenbeck) semigroup generator
diagonalized in this basis. Built on top of the multi-index Hermite
infrastructure in `SchwartzNuclear.HermiteTensorProduct`.

## Motivation

For analysis on `L²(ℝ^d, OU measure)` (Gaussian measure with covariance K⁻¹),
the natural basis is the **K-Hermite functions** — Hermite functions in the
K^{1/2}-rescaled coordinates. They form an orthonormal basis and diagonalize
the OU semigroup generator `L_OU = (1/2) K⁻¹·∇² − u·∇`.

For continuity-method existence proofs (e.g., the QHJ formalism for
lattice gauge theories), one wants:

* A finite-dimensional **Galerkin truncation**: project a phase function
  onto Hermite levels of total degree `≤ d_max`. The truncation gives a
  finite system of polynomial equations on `ℝ^N`, where
  `N = #{α : MultiIndex d | α.abs ≤ d_max}`.
* The **OU generator** acts diagonally on this truncated space, with
  eigenvalues `α.abs : ℕ`. Combined with the saddle-shift `O(1/√N)`
  perturbation, this lets the linearization invertibility be done by
  Neumann series.
* **Implicit function theorem in finite dimensions** then gives a smooth
  (or analytic) family of solutions parameterized by t.

This file provides:

* `MultiIndex.below d_max d` — the Finset of multi-indices α : Fin d → ℕ
  with `α.abs ≤ d_max`. Finite and decidable.
* `hermiteGalerkinTrunc d_max d f` — Galerkin projection of a Schwartz
  function `f` onto the truncated Hermite basis.
* `OU.generator_acts_diagonally` — the OU generator's eigenvalue formula
  (as a statement; body to be filled in via the existing harmonic
  oscillator infrastructure in `SchwartzHermiteExpansion`).
* `hermiteGalerkinTrunc_tendsto` — convergence as `d_max → ∞` (statement).

## Status (2026-05-02)

**Skeleton**: definitions and statements without proofs. The bodies are
mechanical or follow from existing `SchwartzNuclear.Hermite*` infrastructure
plus standard Mathlib finiteness / convergence lemmas. Discharge planned
for the QHJ formalization downstream.

## References

* Bogachev, *Gaussian Measures*, AMS, 1998 — OU semigroup, Hermite basis.
* Bakry, Gentil, Ledoux, *Analysis and Geometry of Markov Diffusion
  Operators*, Springer, 2014 — OU generator and Wick polynomials.
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

/-- **Hermite-Galerkin truncation** at degree `d_max`. -/
noncomputable def hermiteGalerkinTrunc {d : ℕ} (d_max : ℕ)
    (f : SchwartzMap (Fin d → ℝ) ℝ) : SchwartzMap (Fin d → ℝ) ℝ :=
  -- Finite sum over the truncation set.
  -- TODO: explicit formula via SchwartzMap algebra structure +
  -- Finset.sum of (hermiteCoeffNd d α f) • (schwartzHermiteBasisNd d α).
  -- Statement-only here; body filled in once schwartzHermiteBasisNd's
  -- multi-index API is exposed in HermiteTensorProduct's public surface
  -- (it currently is, but the Finset.sum machinery needs tying together).
  0  -- placeholder; real def is the multi-index sum

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
    (f : SchwartzMap (Fin d → ℝ) ℝ) : Prop :=
  Filter.Tendsto (fun d_max : ℕ => hermiteGalerkinTrunc d_max f)
    Filter.atTop (nhds f)

/-! ## OU semigroup generator on the Hermite basis

The Ornstein-Uhlenbeck semigroup on `L²(ℝ^d, γ_d)` (where `γ_d` is the
standard Gaussian measure) has generator

  `L_OU f = Δ f - x · ∇ f`

This generator is **diagonal in the Hermite basis**: for the multi-index
Hermite function `H_α` (in the convention where `H_α` is the product of
1D Hermite polynomials normalized to be orthonormal in `L²(γ_d)`),

  `L_OU H_α = -|α| · H_α`

where `|α| = α.abs` is the L¹-norm of the multi-index.

This diagonalization is the cornerstone of the QHJ continuity-method
discharge: the Φ-derivative of the QHJ residual at `Φ ≡ 0` is
essentially `L_OU + lower-order`, so its inverse on the Galerkin
subspace is `Σ_α (-|α|)⁻¹ · (projection onto α-eigenspace)`, computable
in closed form.

The connection to the existing `hermiteFunction_harmonic_oscillator_eigenvalue`
(in `SchwartzHermiteExpansion`): the OU generator `L_OU` is conjugate to
the harmonic oscillator `H_HO = -d²/du² + u²` via the similarity
transform `e^{-u²/4} L_OU e^{u²/4} = (-H_HO + 1)/2` (1D case). So
diagonalization of `H_HO` (already proved) implies diagonalization of
`L_OU` after a change of basis; the eigenvalue map is
`H_HO eigenvalue (2n+1)/2 ↔ L_OU eigenvalue −n`. -/

/-- **The OU generator's eigenvalue on multi-index Hermite functions**
(statement; body via similarity transform from
`hermiteFunction_harmonic_oscillator_eigenvalue` + multi-index tensor
product). -/
def OU_generator_acts_diagonally_holds (d : ℕ) (α : MultiIndex d) : Prop :=
  -- For the multi-index Hermite function `hermiteFunctionNd d α`, the
  -- OU generator (acting via Δ - x · ∇) has eigenvalue -α.abs.
  -- Stated as a Prop here; body uses the existing harmonic oscillator
  -- eigenvalue + similarity transform.
  True   -- placeholder; real statement is the eigenvalue equation

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

/-- **Coefficient extraction** for the Galerkin space. Given a Schwartz
`f`, return the vector of Hermite coefficients indexed by
`MultiIndex.below d_max d`. -/
noncomputable def galerkinCoeffs {d : ℕ} (d_max : ℕ)
    (_f : SchwartzMap (Fin d → ℝ) ℝ) :
    MultiIndex.below d_max d → ℝ :=
  -- Statement-only: real def is `fun α => hermiteCoeffNd d α.val f`.
  fun _ => 0

/-! ## Status

This file provides definitions and statement-Props for the API.
Discharge tasks (deferred):

* `hermiteGalerkinTrunc` body (~30 LOC): explicit Finset.sum.
* `hermiteGalerkinTrunc_tendsto_schwartz` proof (~80 LOC): exhaustion
  of partial sums + rapid-decay summability.
* `OU_generator_acts_diagonally` proof (~150 LOC): similarity transform
  from the existing harmonic oscillator eigenvalue.
* `galerkinCoeffs` body (~10 LOC): just `hermiteCoeffNd` restricted to
  the truncation Finset.

Discharge of the above unblocks the QHJ Phase B (continuity-method
openness) discharge in `pphi2N`. -/

end GaussianField

end
