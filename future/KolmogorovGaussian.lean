/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Algebra.Module.WeakDual

/-!
# Kolmogorov–Minlos Gaussian measure via nuclear L² support (certificate)

This file records the main results of Matteo Cipollina's axiom-free Gaussian measure
construction on the dual of a nuclear space, via the Kolmogorov extension + nuclear L²
support theorem route.

## Mathematical content

Given a nuclear Fréchet space `E` (in the sense of `NuclearSpaceStd`: countable seminorm
family with nuclear inclusions between local Banach completions) and a linear map
`T : E →ₗ[ℝ] H` into a Hilbert space with `‖T ·‖²` continuous, there exists a probability
measure `μ` on `WeakDual ℝ E` (with the cylindrical σ-algebra) satisfying the Gaussian
characteristic functional identity:

  `∫ ω, exp(i ω(f)) dμ = exp(-½ ‖Tf‖²)`   for all `f : E`.

The construction proceeds by:
1. Building a Gaussian process measure on the product space `E → ℝ` via Kolmogorov extension,
   with finite-dimensional Gaussian marginals of covariance `K(f,g) = ⟨Tf, Tg⟩`.
2. Proving the nuclear L² support theorem: using the nuclear inclusion between local Banach
   spaces, the L² evaluation operator admits a nuclear series decomposition, yielding a
   measurable modification whose sample paths are continuous linear functionals a.s.
3. Descending the measure from `E → ℝ` to `WeakDual ℝ E` via the modification, preserving
   the characteristic functional.

## Proof source

The full proofs (0 sorry, 0 axiom, ~5500 lines across 18 files) are in:
  https://github.com/or4nge19/OSforGFF

Key files:
- `OSforGFF/NuclearSpace/Defs.lean` — `IsNuclearMap`, `BanachOfSeminorm`
- `OSforGFF/NuclearSpace/Std.lean` — `NuclearSpaceStd` typeclass
- `OSforGFF/GaussianProcessKolmogorov.lean` — Kolmogorov extension Gaussian
- `OSforGFF/MinlosGaussianSupportNuclearL2.lean` — nuclear L² support theorem
- `OSforGFF/MinlosGaussianProved.lean` — assembly

## Relationship to our construction

Our `GaussianField.Construction` takes a different route: direct series pushforward of iid
Gaussians via the Dynin–Mityagin Schauder basis, landing on `WeakDual` immediately.
`DyninMityaginSpace` is strictly stronger than `NuclearSpaceStd` (it additionally requires
a Schauder basis). For spaces without a known basis (e.g., `𝒟(ℝⁿ) = C_c^∞(ℝⁿ)`, which is
nuclear but not Fréchet), the Kolmogorov route via `NuclearSpaceStd` applies more broadly.
-/

open MeasureTheory Complex

noncomputable section

namespace GaussianField

/-! ## Nuclear space (standard Grothendieck–Pietsch formulation)

A continuous linear map between Banach spaces is **nuclear** if it admits a representation
`T(x) = ∑ₙ φₙ(x) • yₙ` with `∑ₙ ‖φₙ‖ · ‖yₙ‖ < ∞`.

A locally convex space `E` is **nuclear in the standard sense** if its topology is generated
by a countable monotone family of seminorms `p : ℕ → Seminorm ℝ E` such that for every `n`
there exists `m > n` with the canonical inclusion between local Banach completions
`BanachOfSeminorm(p m) → BanachOfSeminorm(p n)` being nuclear. -/

/-- Axiom recording the existence of a Gaussian probability measure on `WeakDual ℝ E`
for any nuclear Fréchet space `E` (in the sense of Cipollina's `NuclearSpaceStd`) and
continuous quadratic form `‖T ·‖²`.

**Proved in**: `OSforGFF.MinlosGaussianProved.exists_gaussianProcessWeakDual_of_nuclear`
at https://github.com/or4nge19/OSforGFF

The hypothesis `NuclearSpaceStd` is weaker than our `DyninMityaginSpace`: it does not
require a Schauder basis, only nuclear inclusions between local Banach completions.

This axiom is not used by the main build path (which uses the DM series construction).
It is recorded here as a certificate of the alternative Kolmogorov route. -/
axiom NuclearSpaceStd : (E : Type*) → [AddCommGroup E] → [Module ℝ E] →
    [TopologicalSpace E] → Prop

axiom kolmogorov_gaussian_measure
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [MeasurableSpace (WeakDual ℝ E)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (hNuc : NuclearSpaceStd E)
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ μ : ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω : WeakDual ℝ E, exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure) =
          exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ))

end GaussianField
