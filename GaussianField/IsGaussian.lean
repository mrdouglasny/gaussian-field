/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# IsGaussian Instance

We show that the Gaussian measure constructed by this library satisfies
Mathlib's `ProbabilityTheory.IsGaussian` typeclass.

## Main results

- `weakDual_clm_eq_eval`: Every continuous linear functional on `WeakDual ℝ E`
  is evaluation at some `f ∈ E`. This is a standard fact: the continuous dual
  of the weak-* topology is the original space.
- `measure_isGaussian`: `IsGaussian (measure T)` for any CLM `T : E →L[ℝ] H`.

## The bridging argument

Mathlib's `IsGaussian μ` requires that `μ.map L` is a real Gaussian for every
`L : StrongDual ℝ (Configuration E)`, i.e., every `L : (WeakDual ℝ E) →L[ℝ] ℝ`.

Since `Configuration E = WeakDual ℝ E` carries the weak-* (initial) topology,
every such `L` is evaluation at some `f ∈ E`:
1. Continuity of `L` w.r.t. the initial topology means `ker L` contains
   the intersection of finitely many evaluation kernels.
2. By linear algebra (`mem_span_of_iInf_ker_le_ker`), `L` is a finite
   linear combination of evaluations.
3. By linearity, `L = ev(∑ cᵢ fᵢ)` for `f = ∑ cᵢ fᵢ`.

Our existing `pairing_is_gaussian` then immediately gives the result.
-/

import GaussianField.Properties
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace Filter Set Topology
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
/--
Every continuous linear functional on `WeakDual ℝ E` is evaluation at some `f ∈ E`.
This is the standard fact that the continuous dual of the weak-* topology
on E' is canonically isomorphic to E itself.
-/
lemma weakDual_clm_eq_eval (L : (WeakDual ℝ E) →L[ℝ] ℝ) :
    ∃ f : E, ∀ ω : WeakDual ℝ E, L ω = ω f := by
  -- The evaluation linear map: ev(f)(ω) = ω(f)
  let ev : E → ((WeakDual ℝ E) →ₗ[ℝ] ℝ) := (topDualPairing ℝ E).flip
  -- The embedding φ(ω)(f) = ω(f) from WeakDual into E → ℝ (product space)
  let φ : WeakDual ℝ E → (E → ℝ) := fun ω f => (topDualPairing ℝ E) ω f
  -- φ is inducing (the WeakDual topology is defined as the induced topology)
  have h_ind : IsInducing φ := ⟨rfl⟩
  -- Step 1: Extract a finite set of test functions from continuity of L
  -- L⁻¹'(Ioo (-1) 1) is a neighborhood of 0 in the weak-* topology
  have h_nhd : L ⁻¹' Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : WeakDual ℝ E) := by
    apply L.continuous.continuousAt.preimage_mem_nhds
    simp only [map_zero]
    exact Ioo_mem_nhds (by norm_num) (by norm_num)
  -- Rewrite using the inducing characterization: nhds = comap φ (nhds (φ 0))
  rw [h_ind.nhds_eq_comap, mem_comap] at h_nhd
  obtain ⟨V, hV_nhd, hV_sub⟩ := h_nhd
  -- φ(0) = 0 (since ω ↦ ω(f) is linear, applied to 0 gives 0)
  have hφ0 : φ 0 = 0 := by ext f; simp [φ]
  rw [hφ0, nhds_pi] at hV_nhd
  -- Extract finite set I and neighborhoods t_f from the pi-filter membership
  obtain ⟨I, t, ht_nhd, hIt_sub⟩ := mem_pi'.mp hV_nhd
  -- Step 2: Show kernel containment via scaling argument
  -- If ω(f) = 0 for all f ∈ I, then L(ω) = 0
  have h_ker : ∀ ω : WeakDual ℝ E, (∀ f ∈ I, ω f = 0) → L ω = 0 := by
    intro ω hω
    by_contra hne
    have hpos : 0 < |L ω| := abs_pos.mpr hne
    obtain ⟨n, hn⟩ := exists_nat_gt |L ω|⁻¹
    -- n • ω has (n • ω) f = n * ω f = n * 0 = 0 ∈ t_f
    have h_mem : φ (n • ω) ∈ (I : Set E).pi t := by
      intro f hf
      -- φ(n • ω)(f) = (topDualPairing ℝ E)(n • ω)(f) = n * ω(f) = n * 0 = 0
      have h0 : φ (n • ω) f = 0 := by
        show (topDualPairing ℝ E) (n • ω) f = 0
        rw [← Nat.cast_smul_eq_nsmul ℝ n ω, map_smul,
          LinearMap.smul_apply, smul_eq_mul, topDualPairing_apply, hω f hf, mul_zero]
      rw [h0]; exact mem_of_mem_nhds (by simpa using ht_nhd f)
    have h_in := hV_sub (hIt_sub h_mem)
    simp only [mem_preimage, mem_Ioo] at h_in
    -- L(n • ω) = n * L(ω)
    have h_Lnω : L (n • ω) = (n : ℝ) * L ω := by
      rw [← Nat.cast_smul_eq_nsmul ℝ n ω, L.map_smul, smul_eq_mul]
    rw [h_Lnω] at h_in
    -- From |L ω|⁻¹ < n and |L ω| > 0, get 1 < n * |L ω|
    have h1 : 1 < (n : ℝ) * |L ω| := by
      have := mul_lt_mul_of_pos_right hn hpos
      simp [inv_mul_cancel₀ (ne_of_gt hpos)] at this
      linarith
    -- But -1 < n * L ω < 1, so |n * L ω| < 1
    -- We have -1 < n * L ω < 1 and 1 < n * |L ω|, contradiction
    by_cases h : 0 ≤ L ω
    · rw [abs_of_nonneg h] at h1; linarith
    · push Not at h; rw [abs_of_neg h] at h1; linarith
  -- Step 3: Reformulate as iInf of kernels ≤ kernel of L
  have h_iInf : ⨅ i : I, LinearMap.ker (ev ↑i) ≤ LinearMap.ker L.toLinearMap := by
    intro ω hω
    rw [LinearMap.mem_ker]
    apply h_ker ω
    intro f hf
    rw [Submodule.mem_iInf] at hω
    exact LinearMap.mem_ker.mp (hω ⟨f, hf⟩)
  -- Step 4: By linear algebra, L is a linear combination of evaluations
  have h_span := mem_span_of_iInf_ker_le_ker h_iInf
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp h_span
  -- Step 5: Construct the witness f = ∑ cᵢ • fᵢ
  refine ⟨∑ i : I, c i • (↑i : E), fun ω => ?_⟩
  -- L(ω) = ∑ cᵢ * ev(fᵢ)(ω) = ∑ cᵢ * ω(fᵢ) = ω(∑ cᵢ • fᵢ)
  -- hc : ∑ i, c i • ev ↑i = ↑L (i.e., L.toLinearMap)
  -- Goal: L ω = ω (∑ i, c i • ↑i)
  have h_eq : L.toLinearMap ω = ∑ i : I, c i * (ev ↑i) ω := by
    have := LinearMap.congr_fun hc ω
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    linarith
  show L.toLinearMap ω = ω (∑ i : I, c i • (↑i : E))
  rw [h_eq, map_sum]
  congr 1; ext ⟨i, hi⟩
  -- Goal: c ⟨i, hi⟩ * (ev i) ω = ω (c ⟨i, hi⟩ • i)
  -- ev i ω = (topDualPairing ℝ E).flip i ω = ω i
  have hev : (ev i) ω = ω i := rfl
  rw [hev, ← smul_eq_mul, map_smul]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-- The measure constructed from `T` is Gaussian in the Mathlib sense:
    its pushforward by every continuous linear functional is a real Gaussian. -/
instance measure_isGaussian (T : E →L[ℝ] H) :
    ProbabilityTheory.IsGaussian (measure T) where
  map_eq_gaussianReal L := by
    obtain ⟨f, hf⟩ := weakDual_clm_eq_eval L
    have h_eq : ⇑L = (fun ω : Configuration E => ω f) := funext hf
    -- Rewrite map, integral, variance using L = ev_f
    simp_rw [show ∀ ω : Configuration E, L ω = ω f from hf, h_eq]
    -- Apply pairing_is_gaussian and centered identity
    rw [pairing_is_gaussian T f, measure_centered T f]
    -- Goal: gaussianReal 0 ⟨Tf,Tf⟩.toNNReal = gaussianReal 0 Var[ev_f].toNNReal
    -- Variance of centered measure = E[X²]
    congr 1
    have h_var : Var[(fun ω : Configuration E => ω f); measure T] =
        ∫ ω, (ω f) ^ 2 ∂(measure T) :=
      variance_of_integral_eq_zero
        (configuration_eval_measurable f).aemeasurable (measure_centered T f)
    rw [h_var, second_moment_eq_covariance T f]

end GaussianField
