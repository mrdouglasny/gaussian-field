/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positive-Time Test Functions on the Cylinder

Defines the submodule of cylinder test functions supported at positive time,
using the 1D Schwartz positive-time submodule from `Cylinder.Symmetry`.

## Main definitions

- `cylinderPositiveTimeSubmodule` — closure of span of pure tensors g ⊗ h
  with h ∈ schwartzPositiveTimeSubmodule
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

open NuclearTensorProduct

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Positive-time submodule -/

/-- The set of positive-time pure tensors: `g ⊗ h` where h vanishes on (-∞, 0]. -/
private def positiveTimePureTensors :
    Set (CylinderTestFunction L) :=
  {f | ∃ (g : SmoothMap_Circle L ℝ) (h : SchwartzMap ℝ ℝ),
    h ∈ schwartzPositiveTimeSubmodule ∧ f = pure g h}

/-- Submodule of cylinder test functions supported at positive time t > 0.

Defined as the topological closure of the span of pure tensors `g ⊗ h`
where `h ∈ schwartzPositiveTimeSubmodule` (i.e., h vanishes on (-∞, 0]).

Mathematically, this is the closure (in the nuclear Fréchet topology) of
finite sums `∑ gᵢ ⊗ hᵢ` where each `hᵢ ∈ 𝓢(ℝ)` has support in (0, ∞).

Key property: if f is positive-time supported, then `cylinderTimeReflection L f`
is negative-time supported (support in (-∞, 0)), and these are disjoint.
This separation is what makes OS3 (reflection positivity) work. -/
def cylinderPositiveTimeSubmodule :
    Submodule ℝ (CylinderTestFunction L) :=
  (Submodule.span ℝ (positiveTimePureTensors L)).topologicalClosure

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
the continuum).

Note: this requires f ≠ 0 since Θ0 = 0 is in every submodule. -/
axiom cylinderPositiveTime_disjoint_reflected
    (f : CylinderPositiveTimeTestFunction L) (hf : f.val ≠ 0) :
    cylinderTimeReflection L f.val ∉ cylinderPositiveTimeSubmodule L

/-! ## Positive-time support under translation

Time translation by τ > 0 maps positive-time functions to positive-time
functions (shifts support further into the future). Time translation by
τ < 0 can move support to include t ≤ 0, breaking the positive-time property.

Spatial translation preserves the positive-time property since it acts
only on the S¹ factor and leaves the temporal support unchanged. -/

/-- Spatial translation maps positive-time pure tensors to positive-time
pure tensors: `T_v(g ⊗ h) = (T_v g) ⊗ h`, preserving the temporal factor. -/
private theorem spatialTranslation_maps_generators (v : ℝ)
    {f : CylinderTestFunction L} (hf : f ∈ positiveTimePureTensors L) :
    cylinderSpatialTranslation L v f ∈ positiveTimePureTensors L := by
  obtain ⟨g, h, hh, rfl⟩ := hf
  refine ⟨circleTranslation L v g, h, hh, ?_⟩
  show nuclearTensorProduct_mapCLM (circleTranslation L v)
    (ContinuousLinearMap.id ℝ _) (pure g h) = pure (circleTranslation L v g) h
  rw [nuclearTensorProduct_mapCLM_pure]
  simp

/-- Spatial translation preserves positive-time support.

Proof: spatial translation `T_v ⊗ id` maps pure tensors `g ⊗ h ↦ (T_v g) ⊗ h`,
preserving the temporal factor h. So it maps the generating set into itself,
hence the span, hence (by continuity) the closure. -/
theorem cylinderPositiveTime_spatialTranslation_closed (v : ℝ)
    (f : CylinderPositiveTimeTestFunction L) :
    cylinderSpatialTranslation L v f.val ∈ cylinderPositiveTimeSubmodule L := by
  -- Strategy: show the CLM maps the closure into itself via topologicalClosure_minimal
  set S := Submodule.span ℝ (positiveTimePureTensors L)
  set T := cylinderSpatialTranslation L v
  -- The comap of the closure under T is a closed submodule containing S
  set M := cylinderPositiveTimeSubmodule L  -- = S.topologicalClosure
  suffices h : S.topologicalClosure ≤ M.comap T.toLinearMap from
    (h f.property : T f.val ∈ M)
  apply Submodule.topologicalClosure_minimal
  · -- S ≤ M.comap T, i.e., T maps span of generators into M
    intro x hx
    show T x ∈ M
    -- It suffices to show T maps span of generators into span of generators
    suffices T x ∈ S from subset_closure this
    -- Induction on the span: T maps generators to generators, rest by linearity
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (spatialTranslation_maps_generators L v hx)
    | zero => simp
    | add x y _ _ hTx hTy => rw [map_add]; exact Submodule.add_mem S hTx hTy
    | smul r x _ hTx => rw [map_smul]; exact Submodule.smul_mem S r hTx
  · -- M.comap T is closed (continuous preimage of closed set)
    exact (Submodule.isClosed_topologicalClosure S).preimage T.continuous

end GaussianField
