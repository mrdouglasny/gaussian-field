/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Positive-Time Test Functions on the Cylinder

Defines the submodule of cylinder test functions supported at positive time,
using the 1D Schwartz positive-time submodule from `Cylinder.Symmetry`.

## Main definitions

- `cylinderPositiveTimeSubmodule` — closure of span of pure tensors g ⊗ h
  with h ∈ schwartzPositiveTimeSubmodule
- `cylinderNegativeTimeSubmodule` — closure of span of pure tensors g ⊗ h
  with h ∈ schwartzNegativeTimeSubmodule
- `CylinderPositiveTimeTestFunction` — elements of the positive-time submodule

## Main results

- `cylinderTimeReflection_pos_to_neg` — Θ maps P+ into N− (proved)
- `cylinderPositiveTime_disjoint_reflected` — Θf ∉ P+ for nonzero f ∈ P+ (proved)
- `cylinderPositiveTime_spatialTranslation_closed` — spatial translation preserves P+ (proved)

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

/-! ## Negative-time submodule -/

/-- The set of negative-time pure tensors: `g ⊗ h` where h vanishes on [0, ∞). -/
private def negativeTimePureTensors :
    Set (CylinderTestFunction L) :=
  {f | ∃ (g : SmoothMap_Circle L ℝ) (h : SchwartzMap ℝ ℝ),
    h ∈ schwartzNegativeTimeSubmodule ∧ f = pure g h}

/-- Submodule of cylinder test functions supported at negative time t < 0.

Defined as the topological closure of the span of pure tensors `g ⊗ h`
where `h ∈ schwartzNegativeTimeSubmodule` (i.e., h vanishes on [0, ∞)). -/
def cylinderNegativeTimeSubmodule :
    Submodule ℝ (CylinderTestFunction L) :=
  (Submodule.span ℝ (negativeTimePureTensors L)).topologicalClosure

/-! ## Time reflection maps P+ to N+ -/

/-- Time reflection maps positive-time pure tensors to negative-time pure tensors:
`Θ(g ⊗ h) = g ⊗ Θh`, and if h vanishes on (-∞, 0] then Θh vanishes on [0, ∞). -/
private theorem timeReflection_maps_pos_to_neg
    {f : CylinderTestFunction L} (hf : f ∈ positiveTimePureTensors L) :
    cylinderTimeReflection L f ∈ negativeTimePureTensors L := by
  obtain ⟨g, h, hh, rfl⟩ := hf
  refine ⟨g, schwartzReflection h, ?_, ?_⟩
  · exact schwartzReflection_positive_to_negative hh
  · show nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ _)
      schwartzReflection (pure g h) = pure g (schwartzReflection h)
    rw [nuclearTensorProduct_mapCLM_pure]
    simp

/-- Time reflection maps the positive-time submodule into the negative-time submodule.

Proof: Θ maps positive-time generators `g ⊗ h` to negative-time generators
`g ⊗ Θh`, hence the span, hence (by continuity) the closure. -/
theorem cylinderTimeReflection_pos_to_neg
    (f : CylinderPositiveTimeTestFunction L) :
    cylinderTimeReflection L f.val ∈ cylinderNegativeTimeSubmodule L := by
  set S := Submodule.span ℝ (positiveTimePureTensors L)
  set Θ := cylinderTimeReflection L
  set N := cylinderNegativeTimeSubmodule L
  suffices h : S.topologicalClosure ≤ N.comap Θ.toLinearMap from
    (h f.property : Θ f.val ∈ N)
  apply Submodule.topologicalClosure_minimal
  · intro x hx
    show Θ x ∈ N
    suffices Θ x ∈ Submodule.span ℝ (negativeTimePureTensors L) from subset_closure this
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (timeReflection_maps_pos_to_neg L hx)
    | zero => simp
    | add x y _ _ hTx hTy => rw [map_add]; exact Submodule.add_mem _ hTx hTy
    | smul r x _ hTx => rw [map_smul]; exact Submodule.smul_mem _ r hTx
  · exact (Submodule.isClosed_topologicalClosure _).preimage Θ.continuous

/-! ## Slice extraction CLMs

For fixed `a : ℕ`, we extract the "a-th slice" of a cylinder test function:
the subsequence `b ↦ f.val(Nat.pair a b)`. This maps `RapidDecaySeq → RapidDecaySeq`
and, composed with `schwartzRapidDecayEquiv1D.symm`, gives a CLM to `SchwartzMap ℝ ℝ`.

The key property is that slicing a pure tensor `pure g h` at index `a` yields
`coeff a g • h`, where `coeff a g` is the a-th DM coefficient of `g`. -/

/-- Extract the a-th slice: `b ↦ f.val(Nat.pair a b)`.
This is rapidly decaying because `b ≤ Nat.pair a b`. -/
private theorem pair_weight_le (a b : ℕ) (k : ℕ) :
    (1 + (b : ℝ)) ^ k ≤ (1 + (Nat.pair a b : ℝ)) ^ k := by
  apply pow_le_pow_left₀ (by positivity)
  have h : b ≤ Nat.pair a b := Nat.right_le_pair a b
  have : (b : ℝ) ≤ (Nat.pair a b : ℝ) := Nat.cast_le (α := ℝ).mpr h
  linarith

private theorem pair_right_injective (a : ℕ) :
    Function.Injective (Nat.pair a) := by
  intro b₁ b₂ h
  exact (Nat.pair_eq_pair.mp h).2

private def ntpExtractSliceFun (a : ℕ) (f : RapidDecaySeq) : RapidDecaySeq where
  val b := f.val (Nat.pair a b)
  rapid_decay k := by
    set g : ℕ → ℝ := fun m => |f.val m| * (1 + (m : ℝ)) ^ k
    apply Summable.of_nonneg_of_le
    · intro b; exact mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg b k)
    · intro b
      show |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k ≤ g (Nat.pair a b)
      exact mul_le_mul_of_nonneg_left (pair_weight_le a b k) (abs_nonneg _)
    · exact (f.rapid_decay k).comp_injective (pair_right_injective a)

private def ntpExtractSliceLM (a : ℕ) : RapidDecaySeq →ₗ[ℝ] RapidDecaySeq where
  toFun := ntpExtractSliceFun a
  map_add' f g := RapidDecaySeq.ext fun b => by
    show (f + g).val (Nat.pair a b) = (ntpExtractSliceFun a f + ntpExtractSliceFun a g).val b
    simp [ntpExtractSliceFun, RapidDecaySeq.add_val]
  map_smul' r f := RapidDecaySeq.ext fun b => by
    show (r • f).val (Nat.pair a b) = (r • ntpExtractSliceFun a f).val b
    simp [ntpExtractSliceFun, RapidDecaySeq.smul_val]

private theorem ntpExtractSliceLM_isBounded (a : ℕ) :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      RapidDecaySeq.rapidDecaySeminorm (ntpExtractSliceLM a) := by
  intro k
  refine ⟨{k}, 1, fun f => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, one_smul]
  show ∑' b, |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k ≤
    ∑' m, |f.val m| * (1 + (m : ℝ)) ^ k
  set h₁ : ℕ → ℝ := fun b => |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k
  set h₂ : ℕ → ℝ := fun b => |f.val (Nat.pair a b)| * (1 + (Nat.pair a b : ℝ)) ^ k
  have h₁_sum : Summable h₁ := (ntpExtractSliceFun a f).rapid_decay k
  have h₂_sum : Summable h₂ := (f.rapid_decay k).comp_injective (pair_right_injective a)
  calc ∑' b, h₁ b
      ≤ ∑' b, h₂ b :=
        h₁_sum.tsum_le_tsum
          (fun b => mul_le_mul_of_nonneg_left (pair_weight_le a b k) (abs_nonneg _)) h₂_sum
    _ ≤ ∑' m, |f.val m| * (1 + (m : ℝ)) ^ k :=
        tsum_comp_le_tsum_of_inj (f.rapid_decay k)
          (fun m => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg m k))
          (pair_right_injective a)

private def ntpExtractSlice (a : ℕ) : RapidDecaySeq →L[ℝ] RapidDecaySeq where
  toLinearMap := ntpExtractSliceLM a
  cont := WithSeminorms.continuous_of_isBounded
    RapidDecaySeq.rapidDecay_withSeminorms
    RapidDecaySeq.rapidDecay_withSeminorms
    (ntpExtractSliceLM a) (ntpExtractSliceLM_isBounded a)

@[simp]
private theorem ntpExtractSlice_val (a : ℕ) (f : RapidDecaySeq) (b : ℕ) :
    (ntpExtractSlice a f).val b = f.val (Nat.pair a b) := rfl

/-- Compose extraction with `schwartzRapidDecayEquiv1D.symm` to get a CLM
from `CylinderTestFunction L` to `SchwartzMap ℝ ℝ`. -/
private def ntpSliceSchwartz (a : ℕ) :
    CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ :=
  schwartzRapidDecayEquiv1D.symm.toContinuousLinearMap.comp (ntpExtractSlice a)

/-! ## Slice of pure tensors -/

/-- Slicing a pure tensor at index `a` yields `coeff_a(g) • h`.

For `pure g h`:
- `(pure g h).val (Nat.pair a b) = coeff a g * coeff b h`
  (by `NuclearTensorProduct.pure_val` and `Nat.unpair_pair`)
- The extracted slice is `b ↦ coeff_a(g) * coeff_b(h) = coeff_a(g) • (equiv h).val b`
- Applying `equiv.symm` gives `coeff_a(g) • h` -/
private theorem ntpSliceSchwartz_pure (a : ℕ)
    (g : SmoothMap_Circle L ℝ) (h : SchwartzMap ℝ ℝ) :
    ntpSliceSchwartz L a (NuclearTensorProduct.pure g h) =
      DyninMityaginSpace.coeff a g • h := by
  -- Step 1: Show the extracted slice equals coeff_a(g) • equiv(h) as RapidDecaySeq
  have h_extract : ntpExtractSlice a (NuclearTensorProduct.pure g h) =
      DyninMityaginSpace.coeff a g • schwartzRapidDecayEquiv1D h := by
    apply RapidDecaySeq.ext; intro b
    simp only [ntpExtractSlice_val, NuclearTensorProduct.pure_val,
      Nat.unpair_pair, RapidDecaySeq.smul_val]
    -- coeff b h = (schwartzRapidDecayEquiv1D h).val b by definition of ofRapidDecayEquiv
    rfl
  -- Step 2: Apply equiv.symm
  show schwartzRapidDecayEquiv1D.symm (ntpExtractSlice a (NuclearTensorProduct.pure g h)) =
    DyninMityaginSpace.coeff a g • h
  rw [h_extract, map_smul, ContinuousLinearEquiv.symm_apply_apply]

/-! ## Slices preserve time submodules -/

/-- The slice CLM maps `cylinderPositiveTimeSubmodule` into
`schwartzPositiveTimeSubmodule`. -/
private theorem ntpSliceSchwartz_maps_positive (a : ℕ)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) :
    ntpSliceSchwartz L a f ∈ schwartzPositiveTimeSubmodule := by
  -- Strategy: show preimage of schwartzPositiveTimeSubmodule under the CLM is closed,
  -- contains the generators, hence contains the topological closure.
  set S := Submodule.span ℝ (positiveTimePureTensors L)
  set Φ := ntpSliceSchwartz L a
  set P := schwartzPositiveTimeSubmodule
  -- It suffices to show S.topologicalClosure ≤ P.comap Φ.toLinearMap
  suffices h : S.topologicalClosure ≤ P.comap Φ.toLinearMap from h hf
  apply Submodule.topologicalClosure_minimal
  · -- S ≤ P.comap Φ: the CLM maps generators into P
    intro x hx
    show Φ x ∈ P
    -- Induction on the span
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, h, hh, rfl⟩ := hx
      rw [ntpSliceSchwartz_pure]
      exact Submodule.smul_mem P _ hh
    | zero => simp [map_zero, Submodule.zero_mem P]
    | add x y _ _ hΦx hΦy => rw [map_add]; exact Submodule.add_mem P hΦx hΦy
    | smul r x _ hΦx => rw [map_smul]; exact Submodule.smul_mem P r hΦx
  · -- P.comap Φ is closed (continuous preimage of closed set)
    exact schwartzPositiveTimeSubmodule_isClosed.preimage Φ.continuous

/-- The slice CLM maps `cylinderNegativeTimeSubmodule` into
`schwartzNegativeTimeSubmodule`. -/
private theorem ntpSliceSchwartz_maps_negative (a : ℕ)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderNegativeTimeSubmodule L) :
    ntpSliceSchwartz L a f ∈ schwartzNegativeTimeSubmodule := by
  set S := Submodule.span ℝ (negativeTimePureTensors L)
  set Φ := ntpSliceSchwartz L a
  set N := schwartzNegativeTimeSubmodule
  suffices h : S.topologicalClosure ≤ N.comap Φ.toLinearMap from h hf
  apply Submodule.topologicalClosure_minimal
  · intro x hx
    show Φ x ∈ N
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, h, hh, rfl⟩ := hx
      rw [ntpSliceSchwartz_pure]
      exact Submodule.smul_mem N _ hh
    | zero => simp [map_zero, Submodule.zero_mem N]
    | add x y _ _ hΦx hΦy => rw [map_add]; exact Submodule.add_mem N hΦx hΦy
    | smul r x _ hΦx => rw [map_smul]; exact Submodule.smul_mem N r hΦx
  · exact schwartzNegativeTimeSubmodule_isClosed.preimage Φ.continuous

/-! ## 1D disjointness of positive and negative time Schwartz submodules -/

/-- The positive-time and negative-time Schwartz submodules are disjoint:
if h vanishes on (-∞,0] AND on [0,∞) then h = 0. -/
private theorem schwartz_posNeg_disjoint :
    schwartzPositiveTimeSubmodule ⊓ schwartzNegativeTimeSubmodule = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro h ⟨hpos, hneg⟩
  ext x
  simp only [SchwartzMap.zero_apply]
  by_cases hx : x ≤ 0
  · exact hpos x hx
  · push_neg at hx; exact hneg x (le_of_lt hx)

/-! ## Disjointness of positive-time and negative-time submodules -/

/-- The positive-time and negative-time submodules are disjoint.

This is the fundamental temporal separation property: a nonzero element
cannot simultaneously be in the closure of positive-time and negative-time
pure tensors. It follows from the NTP coefficient structure (Cantor-paired
DM expansion) and the 1D result `schwartzPositiveTime_disjoint_reflected`
that positive-time and negative-time Schwartz functions have trivial
intersection. -/
theorem cylinderPositiveTime_negativeTime_disjoint :
    cylinderPositiveTimeSubmodule L ⊓ cylinderNegativeTimeSubmodule L = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f ⟨hf_pos, hf_neg⟩
  -- Each slice of f is in both positive and negative time
  have h_slice_zero : ∀ a, ntpSliceSchwartz L a f = 0 := by
    intro a
    have h_pos := ntpSliceSchwartz_maps_positive L a f hf_pos
    have h_neg := ntpSliceSchwartz_maps_negative L a f hf_neg
    have h_mem : ntpSliceSchwartz L a f ∈
        schwartzPositiveTimeSubmodule ⊓ schwartzNegativeTimeSubmodule :=
      ⟨h_pos, h_neg⟩
    rw [schwartz_posNeg_disjoint] at h_mem
    exact (Submodule.mem_bot ℝ).mp h_mem
  -- All slices zero means all coefficients at paired indices are zero
  have h_val_pair : ∀ a b, f.val (Nat.pair a b) = 0 := by
    intro a b
    have h := h_slice_zero a
    -- ntpSliceSchwartz L a f = equiv.symm (ntpExtractSlice a f) = 0
    -- So ntpExtractSlice a f = equiv 0 = 0
    -- So (ntpExtractSlice a f).val b = 0
    -- i.e. f.val (Nat.pair a b) = 0
    have h2 : ntpExtractSlice a f = 0 := by
      have h1 : schwartzRapidDecayEquiv1D.symm (ntpExtractSlice a f) = 0 := h
      rw [← map_zero schwartzRapidDecayEquiv1D.symm] at h1
      exact schwartzRapidDecayEquiv1D.symm.injective h1
    have h3 : (ntpExtractSlice a f).val b = (0 : RapidDecaySeq).val b := by
      rw [h2]
    simpa using h3
  -- Since Nat.pair is surjective, f.val m = 0 for all m
  apply RapidDecaySeq.ext
  intro m
  show f.val m = (0 : RapidDecaySeq).val m
  rw [RapidDecaySeq.zero_val]
  have := h_val_pair (Nat.unpair m).1 (Nat.unpair m).2
  rwa [Nat.pair_unpair] at this

/-- Time reflection maps the positive-time submodule to a disjoint submodule.

If f has temporal support in (0, ∞), then Θf has temporal support in (-∞, 0).
In particular, f and Θf have disjoint temporal supports.

Proof: if Θf were also in P+, then Θf ∈ P+ ∩ N+ = {0} (since we proved
Θf ∈ N+ from f ∈ P+). So Θf = 0, hence f = Θ(Θf) = 0.

Note: this requires f ≠ 0 since Θ0 = 0 is in every submodule. -/
theorem cylinderPositiveTime_disjoint_reflected
    (f : CylinderPositiveTimeTestFunction L) (hf : f.val ≠ 0) :
    cylinderTimeReflection L f.val ∉ cylinderPositiveTimeSubmodule L := by
  intro hΘf_pos
  apply hf
  -- Θf ∈ N+ (from P+ → N+ theorem)
  have hΘf_neg := cylinderTimeReflection_pos_to_neg L f
  -- Θf ∈ P+ ∩ N+ = {0}, so Θf = 0
  have hΘf_zero : cylinderTimeReflection L f.val = 0 := by
    have hmem : cylinderTimeReflection L f.val ∈
        cylinderPositiveTimeSubmodule L ⊓ cylinderNegativeTimeSubmodule L :=
      ⟨hΘf_pos, hΘf_neg⟩
    rw [cylinderPositiveTime_negativeTime_disjoint L] at hmem
    exact (Submodule.mem_bot ℝ).mp hmem
  -- f = Θ(Θf) = Θ(0) = 0
  have hinv := ContinuousLinearMap.ext_iff.mp (cylinderTimeReflection_involution L) f.val
  simp [ContinuousLinearMap.comp_apply] at hinv
  rw [← hinv, hΘf_zero, map_zero]

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
