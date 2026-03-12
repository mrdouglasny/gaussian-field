/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positive-Time Test Functions on the Cylinder

Defines the submodule of cylinder test functions supported at positive time.

## Main definitions

- `cylinderPositiveTimeSubmodule` — test functions with temporal support in (0, ∞)
- `CylinderPositiveTimeTestFunction` — elements of the positive-time submodule

## Mathematical background

On the cylinder S¹_L × ℝ, "positive time" means the temporal coordinate
t ∈ (0, ∞) ⊂ ℝ. This is the natural half-space for the Osterwalder-Schrader
axioms:

- Time reflection Θ maps t ↦ -t, so support in (0,∞) maps to (-∞,0)
- Positive-time and negative-time supports are disjoint (no wraparound)
- The block-zero property of the mass operator holds automatically:
  if f has support in (0,∞) and Θg has support in (-∞,0), then
  the coupling ⟨f, Q(Θg)⟩ vanishes by locality

This is much cleaner than the torus case, where positive time
means t ∈ (0, L/2) ⊂ ℝ/Lℤ and wraparound must be handled.

## References

- Osterwalder-Schrader (1973), Axiom (A3)
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Cylinder.Symmetry

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Positive-time submodule -/

/-- Submodule of cylinder test functions supported at positive time t > 0.

Since `CylinderTestFunction L` is a nuclear tensor product `C∞(S¹_L) ⊗̂ 𝓢(ℝ)`
without direct pointwise evaluation, we axiomatize the submodule structure.

Mathematically, this is the closure (in the nuclear Fréchet topology) of
finite sums `∑ gᵢ ⊗ hᵢ` where each `hᵢ ∈ 𝓢(ℝ)` has support in (0, ∞).

Key property: if f is positive-time supported, then `cylinderTimeReflection L f`
is negative-time supported (support in (-∞, 0)), and these are disjoint.
This separation is what makes OS3 (reflection positivity) work. -/
axiom cylinderPositiveTimeSubmodule :
    Submodule ℝ (CylinderTestFunction L)

/-- Positive-time test functions on the cylinder.

These are the test functions with temporal support in the open half-line (0, ∞).
For pure tensors g ⊗ h, this means supp(h) ⊂ (0, ∞). -/
abbrev CylinderPositiveTimeTestFunction :=
    cylinderPositiveTimeSubmodule L

/-- Time reflection maps the positive-time submodule to a disjoint submodule.

If f has temporal support in (0, ∞), then Θf has temporal support in (-∞, 0).
In particular, f and Θf have disjoint temporal supports. This is the
fundamental property needed for OS3: the cross terms vanish because the
mass operator Q is local (finite-range on the lattice, differential in
the continuum). -/
axiom cylinderPositiveTime_disjoint_reflected
    (f : CylinderPositiveTimeTestFunction L) :
    cylinderTimeReflection L f.val ∉ cylinderPositiveTimeSubmodule L

/-! ## Positive-time support under translation

Time translation by τ > 0 maps positive-time functions to positive-time
functions (shifts support further into the future). Time translation by
τ < 0 can move support to include t ≤ 0, breaking the positive-time property.

Spatial translation preserves the positive-time property since it acts
only on the S¹ factor and leaves the temporal support unchanged. -/

/-- Spatial translation preserves positive-time support. -/
axiom cylinderPositiveTime_spatialTranslation_closed (v : ℝ)
    (f : CylinderPositiveTimeTestFunction L) :
    cylinderSpatialTranslation L v f.val ∈ cylinderPositiveTimeSubmodule L

end GaussianField
