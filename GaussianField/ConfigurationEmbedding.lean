/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Configuration Space Embedding into ℝ^ℕ

Embeds `Configuration E` into `ℕ → ℝ` via the DM basis, and proves a
sequential Prokhorov theorem for Configuration spaces that avoids
the need for `PolishSpace` or `BorelSpace` instances on `Configuration E`.

## Main definitions

- `configBasisEval` — embedding `Configuration E → (ℕ → ℝ)` via DM basis
- `prokhorov_configuration` — sequential Prokhorov for Configuration spaces

## Strategy

The cylindrical σ-algebra on `Configuration E` equals the pullback of the
product σ-algebra on `ℕ → ℝ` through `configBasisEval` (by the DM expansion).
We push forward measures to `ℕ → ℝ` (which is Polish + Borel), apply
Prokhorov there, and pull back the result.

## Sorry status

No sorries.

## Proved results

- `instMeasurableSpaceConfiguration_eq_comap`: The cylindrical σ-algebra equals
  the pullback of the product σ-algebra through `configBasisEval`.
  Key: DM expansion + `measurable_of_tendsto_metrizable` for partial sums.
-/

import GaussianField.Construction
import Nuclear.DyninMityagin
import Nuclear.NuclearSpace
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.TietzeExtension

noncomputable section

namespace GaussianField

open MeasureTheory Filter BoundedContinuousFunction Topology
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

/-! ## Embedding Configuration E into ℝ^ℕ -/

/-- Embedding of `Configuration E` into `ℕ → ℝ` via DM basis evaluation.
    Maps ω to the sequence `(ω(e₀), ω(e₁), ω(e₂), ...)` where eₙ is the
    n-th DM basis vector. -/
def configBasisEval : Configuration E → (ℕ → ℝ) :=
  fun ω n => ω (DyninMityaginSpace.basis n)

/-- Injectivity: if ω₁ and ω₂ agree on all basis vectors, they're equal.
    Follows from the DM expansion: ω(f) = Σ coeff_m(f) * ω(basis_m). -/
theorem configBasisEval_injective :
    Function.Injective (configBasisEval (E := E)) := by
  intro ω₁ ω₂ h
  have hbasis : ∀ m, (ω₁ : E →L[ℝ] ℝ) (DyninMityaginSpace.basis m) =
      (ω₂ : E →L[ℝ] ℝ) (DyninMityaginSpace.basis m) := by
    intro m; exact congr_fun h m
  exact ContinuousLinearMap.ext fun f => by
    have h1 := DyninMityaginSpace.expansion (ω₁ : E →L[ℝ] ℝ) f
    have h2 := DyninMityaginSpace.expansion (ω₂ : E →L[ℝ] ℝ) f
    rw [h1, h2]
    congr 1; ext m; exact congrArg _ (hbasis m)

/-- `configBasisEval` is continuous (each coordinate is weak-* continuous). -/
theorem configBasisEval_continuous :
    Continuous (configBasisEval (E := E)) := by
  apply continuous_pi
  intro n
  exact WeakDual.eval_continuous (DyninMityaginSpace.basis n)

/-- `configBasisEval` is measurable (cylindrical σ-algebra → product σ-algebra). -/
theorem configBasisEval_measurable :
    @Measurable _ _ instMeasurableSpaceConfiguration MeasurableSpace.pi
    (configBasisEval (E := E)) := by
  apply measurable_pi_lambda
  intro n
  exact configuration_eval_measurable (DyninMityaginSpace.basis n)

/-! ## σ-algebra equality -/

/-- The cylindrical σ-algebra on Configuration E equals the pullback
    of the product σ-algebra through configBasisEval.

    The ≥ direction is immediate (each basis evaluation is cylindrical).
    The ≤ direction uses the DM expansion: ω(f) = Σ' m, coeff_m(f) * ω(basis_m),
    so each evaluation ω(f) is product-measurable as a tsum of coordinates. -/
theorem instMeasurableSpaceConfiguration_eq_comap :
    instMeasurableSpaceConfiguration (E := E) =
    MeasurableSpace.comap configBasisEval MeasurableSpace.pi := by
  apply le_antisymm
  · -- ≤ direction: ω(f) is measurable w.r.t. the basis coordinates.
    -- By DM expansion, ω(f) = lim_n Σ_{m<n} coeff_m(f) * ω(basis_m).
    letI meas : MeasurableSpace (Configuration E) :=
      MeasurableSpace.comap (configBasisEval (E := E)) MeasurableSpace.pi
    -- Each basis coordinate is measurable for the comap σ-algebra
    have h_coord : ∀ m : ℕ, Measurable (fun ω : Configuration E =>
        configBasisEval ω m) :=
      fun m => (measurable_pi_apply m).comp (comap_measurable (configBasisEval (E := E)))
    -- Each evaluation ω ↦ ω(f) is measurable as a limit of partial sums
    suffices h_eval : ∀ f' : E, Measurable (fun ω : Configuration E => ω f') by
      exact (measurable_pi_lambda _ h_eval).comap_le
    intro f'
    -- Define partial sums
    let S : ℕ → Configuration E → ℝ := fun n ω =>
      (Finset.range n).sum fun m => DyninMityaginSpace.coeff m f' * configBasisEval ω m
    apply measurable_of_tendsto_metrizable (f := S)
    · -- Each partial sum is measurable
      intro n
      exact Finset.measurable_sum _ fun m _ => (h_coord m).const_mul _
    · -- Partial sums converge to ω(f') by DM expansion
      rw [tendsto_pi_nhds]
      intro ω
      have h := (DyninMityaginSpace.hasSum_basis (E := E) f').mapL (show E →L[ℝ] ℝ from ω)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul] at h
      show Tendsto (fun n => S n ω) atTop (nhds (ω f'))
      exact h.tendsto_sum_nat
  · exact configBasisEval_measurable.comap_le

/-! ## Prokhorov's theorem (sequential version)

Derived from Mathlib's `isCompact_closure_of_isTightMeasureSet`
and the Lévy-Prokhorov metrization of `ProbabilityMeasure X`. -/

/-- **Prokhorov's theorem** (sequential version).
On a Polish space X, if a sequence of probability measures {μₙ} is tight,
then it has a weakly convergent subsequence. -/
theorem prokhorov_sequential {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [PolishSpace X] [BorelSpace X]
    (μ : ℕ → Measure X)
    (hμ_prob : ∀ n, IsProbabilityMeasure (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set X, IsCompact K ∧ ∀ n, 1 - ε ≤ (μ n K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : Measure X),
      StrictMono φ ∧ IsProbabilityMeasure ν ∧
      ∀ (f : X → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (nhds (∫ x, f x ∂ν)) := by
  let P : ℕ → ProbabilityMeasure X := fun n => ⟨μ n, hμ_prob n⟩
  have htight : IsTightMeasureSet
      {((p : ProbabilityMeasure X) : Measure X) | p ∈ Set.range P} := by
    rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · subst hε_top
      obtain ⟨K, hK, _⟩ := hμ_tight 1 one_pos
      exact ⟨K, hK, fun _ _ => le_top⟩
    · have hε_real : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) hε_top
      obtain ⟨K, hK_compact, hK_bound⟩ := hμ_tight ε.toReal hε_real
      refine ⟨K, hK_compact, ?_⟩
      intro ν' hν'
      obtain ⟨_, ⟨n, rfl⟩, rfl⟩ := hν'
      change (μ n) Kᶜ ≤ ε
      have hK_meas : MeasurableSet K := hK_compact.measurableSet
      rw [prob_compl_eq_one_sub hK_meas (μ := μ n)]
      rw [tsub_le_iff_right]
      have hK_fin : (μ n K) ≠ ⊤ := measure_ne_top (μ n) K
      have h_add_fin : ε + (μ n K) ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hε_top, hK_fin⟩
      rw [← ENNReal.ofReal_toReal h_add_fin, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [ENNReal.toReal_add hε_top hK_fin]
      linarith [hK_bound n]
  have hcomp : IsCompact (closure (Set.range P)) :=
    isCompact_closure_of_isTightMeasureSet htight
  have hseq := hcomp.isSeqCompact
  obtain ⟨ν, _, φ, hφ_strict, hφ_tend⟩ :=
    hseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨φ, ν, hφ_strict, ν.prop, ?_⟩
  intro f hf_cont ⟨C, hC⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hφ_tend
  let f_bcf : BoundedContinuousFunction X ℝ :=
    ⟨⟨f, hf_cont⟩, ⟨2 * C, fun x y => by
      rw [Real.dist_eq]
      calc |f x - f y| ≤ |f x| + |f y| := by
            have := norm_sub_le (f x) (f y)
            simp only [Real.norm_eq_abs] at this; exact this
        _ ≤ C + C := add_le_add (hC x) (hC y)
        _ = 2 * C := by ring⟩⟩
  simpa using hφ_tend f_bcf

/-! ## Prokhorov for Configuration spaces

The main theorems: sequential Prokhorov for `Configuration E` without
requiring Polish/Borel instances. Uses the ℝ^ℕ embedding.

Two versions:
- `prokhorov_configuration_pushforward`: fully proved, gives weak convergence
  of pushforward measures on ℕ → ℝ plus concentration on range.
- `prokhorov_configuration`: fully proved, pulls back to Configuration E
  via Tietze extension + DM partial sum approximation for measurability. -/

/-- **Prokhorov's theorem for Configuration spaces (pushforward version).**

For a DyninMityaginSpace E, if a sequence of probability measures on
`Configuration E` is tight, then there exists a subsequence whose
pushforwards to `ℕ → ℝ` converge weakly, with the limit concentrating
on `range(configBasisEval)`.

This version avoids the measure pullback and is fully proved. For
cylinder-function convergence (e.g., ∫ ω(f₁)·ω(f₂) dμₙ → ∫ ... dν),
compose test functions with `configBasisEval` and use `hconv`. -/
theorem prokhorov_configuration_pushforward
    (μ : ℕ → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (hμ_prob : ∀ n, @IsProbabilityMeasure _ instMeasurableSpaceConfiguration (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (Configuration E), IsCompact K ∧
      ∀ n, 1 - ε ≤ ((μ n) K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : Measure (ℕ → ℝ)),
      StrictMono φ ∧ IsProbabilityMeasure ν ∧
      ν (Set.range (configBasisEval (E := E)))ᶜ = 0 ∧
      ∀ (f : (ℕ → ℝ) → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ x, f x ∂(@Measure.map _ _
          instMeasurableSpaceConfiguration _ configBasisEval (μ (φ n))))
          atTop (nhds (∫ x, f x ∂ν)) := by
  -- Step 1: Push forward measures to ℕ → ℝ
  let ν_seq : ℕ → Measure (ℕ → ℝ) := fun n =>
    @Measure.map _ _ instMeasurableSpaceConfiguration _ configBasisEval (μ n)
  -- Step 2: Pushforward measures are probability measures
  have hν_prob : ∀ n, IsProbabilityMeasure (ν_seq n) := by
    intro n; have := hμ_prob n
    exact Measure.isProbabilityMeasure_map
      (configBasisEval_measurable.aemeasurable (μ := μ n))
  -- Step 3: Tightness transfers through continuous maps
  have hν_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (ℕ → ℝ), IsCompact K ∧ ∀ n, 1 - ε ≤ (ν_seq n K).toReal := by
    intro ε hε
    obtain ⟨K, hK_compact, hK_bound⟩ := hμ_tight ε hε
    refine ⟨configBasisEval '' K, hK_compact.image configBasisEval_continuous, ?_⟩
    intro n
    calc 1 - ε ≤ ((μ n) K).toReal := hK_bound n
      _ ≤ (ν_seq n (configBasisEval '' K)).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          rw [show ν_seq n = Measure.map configBasisEval (μ n) from rfl,
              Measure.map_apply configBasisEval_measurable
                (hK_compact.image configBasisEval_continuous).measurableSet]
          exact measure_mono (Set.subset_preimage_image _ _)
  -- Step 4: Apply Prokhorov in ℕ → ℝ (Polish + Borel)
  obtain ⟨φ, ν_lim, hφ, hν_lim_prob, hconv_RN⟩ :=
    prokhorov_sequential ν_seq hν_prob hν_tight
  -- Step 5: Concentration on range(configBasisEval) via Portmanteau
  have h_conc : ν_lim (Set.range (configBasisEval (E := E)))ᶜ = 0 := by
    -- Reconstruct ProbabilityMeasure convergence from integral convergence
    let P_sub : ℕ → ProbabilityMeasure (ℕ → ℝ) :=
      fun n => ⟨ν_seq (φ n), hν_prob (φ n)⟩
    let P_lim : ProbabilityMeasure (ℕ → ℝ) := ⟨ν_lim, hν_lim_prob⟩
    have hPM_tend : Tendsto P_sub atTop (nhds P_lim) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f_bcf
      exact hconv_RN f_bcf f_bcf.continuous
        ⟨‖f_bcf‖, fun x => (Real.norm_eq_abs _).symm ▸ f_bcf.norm_coe_le_norm x⟩
    -- Suffices: ∀ ε > 0, ν_lim(rangeᶜ) ≤ ENNReal.ofReal ε
    apply le_antisymm _ (zero_le _)
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    rw [zero_add]
    -- Get compact K with μ(φ n)(K) ≥ 1 - ε for all n
    have hε_real : (0 : ℝ) < ε := NNReal.coe_pos.mpr hε
    obtain ⟨K, hK_compact, hK_bound⟩ := hμ_tight ε hε_real
    set F := configBasisEval (E := E) '' K with hF_def
    have hF_compact : IsCompact F := hK_compact.image configBasisEval_continuous
    have hF_closed : IsClosed F := hF_compact.isClosed
    have hF_range : F ⊆ Set.range (configBasisEval (E := E)) := Set.image_subset_range _ _
    -- Each ν_seq(φ n)(F) ≥ ENNReal.ofReal(1 - ε)
    have hF_mass : ∀ n, ENNReal.ofReal (1 - (ε : ℝ)) ≤ (P_sub n : Measure (ℕ → ℝ)) F := by
      intro n
      rw [show (P_sub n : Measure _) = ν_seq (φ n) from rfl]
      calc ENNReal.ofReal (1 - (ε : ℝ))
          ≤ ENNReal.ofReal ((μ (φ n) K).toReal) := ENNReal.ofReal_le_ofReal (hK_bound (φ n))
        _ ≤ (μ (φ n)) K := ENNReal.ofReal_toReal_le
        _ ≤ ν_seq (φ n) F := by
            rw [show ν_seq (φ n) = Measure.map configBasisEval (μ (φ n)) from rfl,
                Measure.map_apply configBasisEval_measurable hF_compact.measurableSet]
            exact measure_mono (Set.subset_preimage_image _ _)
    -- Portmanteau (closed set): limsup ≤ ν_lim(F)
    have h_port :=
      ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hPM_tend hF_closed
    -- limsup ≥ ENNReal.ofReal(1-ε) since each term ≥ it
    have h_le_limsup : ENNReal.ofReal (1 - (ε : ℝ)) ≤
        atTop.limsup (fun n => (P_sub n : Measure (ℕ → ℝ)) F) := by
      apply le_limsup_of_frequently_le
      · exact (Eventually.of_forall hF_mass).frequently
      · exact ⟨1, eventually_map.mpr (Eventually.of_forall (fun (n : ℕ) =>
            show (P_sub n : Measure (ℕ → ℝ)) F ≤ 1 from
            (measure_mono (Set.subset_univ F)).trans_eq measure_univ))⟩
    -- ν_lim(F) ≥ ENNReal.ofReal(1-ε)
    have hF_lim : ENNReal.ofReal (1 - (ε : ℝ)) ≤ ν_lim F := h_le_limsup.trans h_port
    -- rangeᶜ ⊆ Fᶜ ⊆ complement bound
    calc ν_lim (Set.range (configBasisEval (E := E)))ᶜ
        ≤ ν_lim Fᶜ := measure_mono (Set.compl_subset_compl.mpr hF_range)
      _ = 1 - ν_lim F := prob_compl_eq_one_sub hF_closed.measurableSet
      _ ≤ 1 - ENNReal.ofReal (1 - (ε : ℝ)) := tsub_le_tsub_left hF_lim 1
      _ ≤ ↑ε := by
          rw [tsub_le_iff_right]
          -- Goal: 1 ≤ ↑ε + ENNReal.ofReal(1-ε)
          by_cases h : (ε : ℝ) ≤ 1
          · have h1 : ↑ε + ENNReal.ofReal (1 - ↑ε) = 1 := by
              rw [← ENNReal.ofReal_coe_nnreal,
                  ← ENNReal.ofReal_add (NNReal.coe_nonneg _) (by linarith),
                  (show (↑ε : ℝ) + (1 - ↑ε) = 1 from by ring), ENNReal.ofReal_one]
            exact h1.symm ▸ le_refl 1
          · push Not at h
            have h1 : (1 : ENNReal) ≤ ↑ε := by
              rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_coe_nnreal]
              exact ENNReal.ofReal_le_ofReal h.le
            exact le_trans h1 (le_add_right le_rfl)
  refine ⟨φ, ν_lim, hφ, hν_lim_prob, h_conc, fun f hf hC => ?_⟩
  exact hconv_RN f hf hC

/-- **Prokhorov's theorem for Configuration spaces.**

For a DyninMityaginSpace E, if a sequence of probability measures on
`Configuration E` is tight, then it has a weakly convergent subsequence.

This avoids requiring `PolishSpace` or `BorelSpace` instances on
`Configuration E`. Instead, it embeds into `ℕ → ℝ` (which is Polish)
via the DM basis and applies standard Prokhorov there.

**Proof outline:**
1. Push forward measures to `ℕ → ℝ` via `configBasisEval`
2. Tightness transfers (continuous image of compact is compact)
3. Apply `prokhorov_sequential` on `ℕ → ℝ` (Polish + Borel)
4. The limit concentrates on `range(configBasisEval)` (by Portmanteau)
5. Pull back via `Measure.comap` using null-measurability of images

**Fully proved.** The weak convergence transfer uses Tietze extension for
bounded continuous functions and DM partial sum approximation to show
continuous functions are strongly measurable w.r.t. the cylindrical σ-algebra. -/
theorem prokhorov_configuration
    (μ : ℕ → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (hμ_prob : ∀ n, @IsProbabilityMeasure _ instMeasurableSpaceConfiguration (μ n))
    (hμ_tight : ∀ ε : ℝ, 0 < ε →
      ∃ K : Set (Configuration E), IsCompact K ∧
      ∀ n, 1 - ε ≤ ((μ n) K).toReal) :
    ∃ (φ : ℕ → ℕ) (ν : @Measure (Configuration E) instMeasurableSpaceConfiguration),
      StrictMono φ ∧ @IsProbabilityMeasure _ instMeasurableSpaceConfiguration ν ∧
      ∀ (f : Configuration E → ℝ), Continuous f → (∃ C, ∀ x, |f x| ≤ C) →
        Tendsto (fun n => ∫ x, f x ∂(μ (φ n))) atTop (nhds (∫ x, f x ∂ν)) := by
  -- Use pushforward version to get subsequence + limit + concentration
  obtain ⟨φ, ν_lim, hφ, hν_lim_prob, h_conc, hconv_RN⟩ :=
    prokhorov_configuration_pushforward μ hμ_prob hμ_tight
  -- Step 1: Null-measurability condition for Measure.comap
  have h_nmeas : ∀ s, @MeasurableSet _ instMeasurableSpaceConfiguration s →
      NullMeasurableSet (configBasisEval (E := E) '' s) ν_lim := by
    intro s hs
    rw [instMeasurableSpaceConfiguration_eq_comap] at hs
    obtain ⟨T, hT, rfl⟩ := hs
    rw [Set.image_preimage_eq_inter_range]
    exact hT.nullMeasurableSet.inter
      (NullMeasurableSet.compl_iff.mp (NullMeasurableSet.of_null h_conc))
  -- Step 2: ν_lim(range) = 1
  have h_range_one : ν_lim (Set.range (configBasisEval (E := E))) = 1 := by
    apply le_antisymm ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)
    calc (1 : ENNReal) = ν_lim Set.univ := measure_univ.symm
      _ = ν_lim (Set.range configBasisEval ∪ (Set.range configBasisEval)ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ ν_lim (Set.range configBasisEval) + ν_lim (Set.range configBasisEval)ᶜ :=
          measure_union_le _ _
      _ = ν_lim (Set.range configBasisEval) := by rw [h_conc, add_zero]
  -- Step 3: Define ν and show it's a probability measure
  let ν := Measure.comap (configBasisEval (E := E)) ν_lim
  have hν_prob : @IsProbabilityMeasure _ instMeasurableSpaceConfiguration ν := by
    constructor
    show Measure.comap configBasisEval ν_lim Set.univ = 1
    rw [Measure.comap_apply₀ configBasisEval ν_lim configBasisEval_injective h_nmeas
        MeasurableSet.univ.nullMeasurableSet, Set.image_univ]
    exact h_range_one
  -- Step 4: map configBasisEval ν = ν_lim
  have h_range_nm : NullMeasurableSet (Set.range (configBasisEval (E := E))) ν_lim :=
    NullMeasurableSet.compl_iff.mp (NullMeasurableSet.of_null h_conc)
  have h_map_eq : @Measure.map _ _ instMeasurableSpaceConfiguration _
      (configBasisEval (E := E)) ν = ν_lim := by
    ext T hT
    rw [Measure.map_apply configBasisEval_measurable hT,
      Measure.comap_apply₀ configBasisEval ν_lim configBasisEval_injective h_nmeas
        (configBasisEval_measurable hT).nullMeasurableSet,
      Set.image_preimage_eq_inter_range]
    have h_split := measure_inter_add_diff₀ T h_range_nm
    rw [show T \ Set.range (configBasisEval (E := E)) =
        T ∩ (Set.range configBasisEval)ᶜ from rfl,
      measure_mono_null Set.inter_subset_right h_conc, add_zero] at h_split
    exact h_split
  -- Step 5: ε/3 argument for integral convergence
  refine ⟨φ, ν, hφ, hν_prob, ?_⟩
  intro f hf_cont ⟨C, hC⟩
  -- If f is not strongly measurable, all integrals are 0 and convergence is trivial
  by_cases hf_sm : StronglyMeasurable f
  · -- f is strongly measurable → integrable w.r.t. all probability measures
    have hC_nn : (0 : ℝ) ≤ C := le_trans (abs_nonneg _) (hC 0)
    have hC1_pos : (0 : ℝ) < C + 1 := by linarith
    rw [Metric.tendsto_atTop]
    intro ε hε
    set δ := ε / (8 * (C + 1)) with hδ_def
    have hδ_pos : 0 < δ := div_pos hε (by positivity)
    obtain ⟨K, hK_compact, hK_mass⟩ := hμ_tight δ hδ_pos
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK_compact
    -- Tietze: extend f|_K to (ℕ → ℝ) via closed embedding
    have he_ce : IsClosedEmbedding (fun (x : K) => configBasisEval (E := E) (↑x)) :=
      (configBasisEval_continuous.comp continuous_subtype_val).isClosedEmbedding
        (configBasisEval_injective.comp Subtype.val_injective)
    let f_K : K →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
      ⟨f ∘ Subtype.val, hf_cont.comp continuous_subtype_val⟩
    obtain ⟨g, hg_norm, hg_ext⟩ :=
      BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding f_K he_ce
    -- g agrees with f on K
    have hg_agree : ∀ ω ∈ K, (g : (ℕ → ℝ) → ℝ) (configBasisEval ω) = f ω := by
      intro ω hω
      have := congr_fun hg_ext ⟨ω, hω⟩
      simp only [Function.comp_apply, f_K, mkOfCompact_apply, ContinuousMap.coe_mk] at this
      exact this
    -- ‖g‖ ≤ C
    have hg_le_C : ‖g‖ ≤ C := by
      rw [hg_norm]
      exact (BoundedContinuousFunction.norm_le hC_nn).mpr fun x => by
        simp only [f_K, BoundedContinuousFunction.mkOfCompact_apply,
          ContinuousMap.coe_mk, Function.comp_apply, Real.norm_eq_abs]
        exact hC x
    -- |g x| ≤ C for all x
    have hg_bound : ∀ x, |g x| ≤ C := fun x =>
      ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm x).trans hg_le_C
    -- Integrability
    have hf_int : ∀ (μ' : Measure (Configuration E)),
        IsProbabilityMeasure μ' → Integrable f μ' := by
      intro μ' hμ'
      exact Integrable.of_bound hf_sm.aestronglyMeasurable C
        (Eventually.of_forall (fun x => (Real.norm_eq_abs _).symm ▸ hC x))
    have hge_sm : StronglyMeasurable (fun ω : Configuration E => g (configBasisEval ω)) :=
      g.continuous.stronglyMeasurable.comp_measurable configBasisEval_measurable
    have hge_int : ∀ (μ' : Measure (Configuration E)),
        IsProbabilityMeasure μ' → Integrable (fun ω : Configuration E => g (configBasisEval ω)) μ' := by
      intro μ' hμ'
      exact Integrable.of_bound hge_sm.aestronglyMeasurable C
        (Eventually.of_forall (fun x => (Real.norm_eq_abs _).symm ▸ hg_bound _))
    -- L = configBasisEval '' K is closed in ℕ → ℝ
    set L := configBasisEval (E := E) '' K
    have hL_closed : IsClosed L := (hK_compact.image configBasisEval_continuous).isClosed
    -- Measurability of K: via K = configBasisEval⁻¹(L) and L is Borel-measurable
    have hK_meas : MeasurableSet K := by
      rw [show K = configBasisEval ⁻¹' L from
        (Set.preimage_image_eq K configBasisEval_injective).symm]
      exact configBasisEval_measurable hL_closed.measurableSet
    -- ν(K) ≥ 1 - δ via Portmanteau
    have hν_K_mass : 1 - δ ≤ (ν K).toReal := by
      -- ν K = ν_lim L via map
      have hν_K_eq : ν K = ν_lim L := by
        rw [show ν K = (Measure.map configBasisEval ν) L from by
          rw [Measure.map_apply configBasisEval_measurable hL_closed.measurableSet,
              Set.preimage_image_eq K configBasisEval_injective], h_map_eq]
      rw [hν_K_eq]
      -- Construct ProbabilityMeasure convergence
      let P_seq : ℕ → ProbabilityMeasure (ℕ → ℝ) := fun n =>
        ⟨Measure.map configBasisEval (μ (φ n)),
          Measure.isProbabilityMeasure_map configBasisEval_measurable.aemeasurable⟩
      let P_lim : ProbabilityMeasure (ℕ → ℝ) := ⟨ν_lim, hν_lim_prob⟩
      have hPM_tend : Tendsto P_seq atTop (nhds P_lim) := by
        rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
        intro f_bcf
        exact hconv_RN f_bcf f_bcf.continuous
          ⟨‖f_bcf‖, fun x => (Real.norm_eq_abs _).symm ▸ f_bcf.norm_coe_le_norm x⟩
      -- Portmanteau closed set: limsup P_seq(n) L ≤ ν_lim L
      have h_port :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hPM_tend hL_closed
      -- Each P_seq n L ≥ ENNReal.ofReal(1 - δ)
      have h_each : ∀ n, ENNReal.ofReal (1 - δ) ≤ (P_seq n : Measure _) L := by
        intro n
        calc ENNReal.ofReal (1 - δ)
            ≤ ENNReal.ofReal ((μ (φ n) K).toReal) := ENNReal.ofReal_le_ofReal (hK_mass (φ n))
          _ ≤ (μ (φ n)) K := ENNReal.ofReal_toReal_le
          _ ≤ (Measure.map configBasisEval (μ (φ n))) L := by
              rw [Measure.map_apply configBasisEval_measurable hL_closed.measurableSet]
              exact measure_mono (Set.subset_preimage_image _ _)
      have h_le_limsup : ENNReal.ofReal (1 - δ) ≤
          atTop.limsup (fun n => (P_seq n : Measure _) L) := by
        apply le_limsup_of_frequently_le
        · exact (Eventually.of_forall h_each).frequently
        · exact ⟨1, eventually_map.mpr (Eventually.of_forall (fun n =>
              (measure_mono (Set.subset_univ L)).trans_eq measure_univ))⟩
      -- ν_lim L ≥ ENNReal.ofReal(1 - δ) → (ν_lim L).toReal ≥ 1 - δ
      have hν_lim_L : ENNReal.ofReal (1 - δ) ≤ ν_lim L := h_le_limsup.trans h_port
      have h_ne_top : ν_lim L ≠ ⊤ := measure_ne_top _ _
      have h1 := ENNReal.toReal_mono h_ne_top hν_lim_L
      by_cases hδ1 : δ ≤ 1
      · rw [ENNReal.toReal_ofReal (by linarith)] at h1; linarith
      · push Not at hδ1; linarith [ENNReal.toReal_nonneg (a := ν_lim L)]
    -- ∫ g d(map e μ(φ n)) → ∫ g dν_lim
    have hg_conv : Tendsto (fun n =>
        ∫ x, g x ∂(Measure.map configBasisEval (μ (φ n)))) atTop
        (nhds (∫ x, g x ∂ν_lim)) :=
      hconv_RN g g.continuous
        ⟨‖g‖, fun x => (Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm x⟩
    rw [Metric.tendsto_atTop] at hg_conv
    obtain ⟨N, hN⟩ := hg_conv (ε / 3) (by linarith)
    -- Change of variables
    have h_chvar_μ : ∀ n,
        ∫ x, g x ∂(Measure.map configBasisEval (μ (φ n))) =
        ∫ ω, g (configBasisEval ω) ∂(μ (φ n)) :=
      fun n => integral_map configBasisEval_measurable.aemeasurable
        g.continuous.aestronglyMeasurable
    have h_chvar_ν : ∫ x, g x ∂ν_lim = ∫ ω, g (configBasisEval ω) ∂ν := by
      rw [← h_map_eq]
      exact integral_map configBasisEval_measurable.aemeasurable
        g.continuous.aestronglyMeasurable
    -- Error bound: |∫ f dμ' - ∫ g∘e dμ'| ≤ 2(C+1)·δ
    have h_err_bound : ∀ (μ' : Measure (Configuration E)),
        IsProbabilityMeasure μ' →
        1 - δ ≤ (μ' K).toReal →
        |∫ ω, f ω ∂μ' - ∫ ω, g (configBasisEval ω) ∂μ'| ≤ 2 * (C + 1) * δ := by
      intro μ' hμ' h_mass
      rw [← integral_sub (hf_int μ' hμ') (hge_int μ' hμ')]
      have h_abs_le : |∫ ω, (f ω - g (configBasisEval ω)) ∂μ'| ≤
          ∫ ω, |f ω - g (configBasisEval ω)| ∂μ' := by
        have := norm_integral_le_integral_norm (f := fun ω => f ω - g (configBasisEval ω)) (μ := μ')
        simp only [Real.norm_eq_abs] at this
        exact this
      have h_ind_le : ∫ ω, |f ω - g (configBasisEval ω)| ∂μ' ≤
          ∫ ω, (2 * (C + 1)) * (Kᶜ).indicator 1 ω ∂μ' := by
        apply integral_mono_of_nonneg
        · exact Eventually.of_forall (fun _ => abs_nonneg _)
        · exact Integrable.of_bound
            ((measurable_const.mul
              (measurable_one.indicator hK_meas.compl)).aestronglyMeasurable)
            (2 * (C + 1))
            (Eventually.of_forall (fun ω => by
              simp only [Set.indicator, Pi.one_apply, Real.norm_eq_abs]
              split_ifs with hω
              · simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (C + 1))]
              · simp; positivity))
        · apply Eventually.of_forall; intro ω
          by_cases hω : ω ∈ K
          · simp [hg_agree ω hω, Set.indicator, hω]
          · simp only [Set.indicator, Set.mem_compl_iff, hω, not_false_eq_true,
                if_true, Pi.one_apply, mul_one]
            calc |f ω - g (configBasisEval ω)|
                ≤ |f ω| + |g (configBasisEval ω)| := by
                  calc |f ω - g (configBasisEval ω)|
                      = |f ω + (-(g (configBasisEval ω)))| := by ring_nf
                    _ ≤ |f ω| + |-(g (configBasisEval ω))| := abs_add_le _ _
                    _ = |f ω| + |g (configBasisEval ω)| := by rw [abs_neg]
              _ ≤ C + C := add_le_add (hC ω) (hg_bound _)
              _ ≤ 2 * (C + 1) := by linarith
      have h_ind_eq : ∫ ω, (2 * (C + 1)) * (Kᶜ).indicator 1 ω ∂μ' =
          2 * (C + 1) * (μ' Kᶜ).toReal := by
        rw [integral_const_mul, integral_indicator_one hK_meas.compl, Measure.real_def]
      have h_compl_le : (μ' Kᶜ).toReal ≤ δ := by
        rw [prob_compl_eq_one_sub hK_meas,
            ENNReal.toReal_sub_of_le
              ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)
              ENNReal.one_ne_top,
            ENNReal.toReal_one]
        linarith
      calc |∫ ω, (f ω - g (configBasisEval ω)) ∂μ'|
          ≤ ∫ ω, |f ω - g (configBasisEval ω)| ∂μ' := h_abs_le
        _ ≤ ∫ ω, (2 * (C + 1)) * (Kᶜ).indicator 1 ω ∂μ' := h_ind_le
        _ = 2 * (C + 1) * (μ' Kᶜ).toReal := h_ind_eq
        _ ≤ 2 * (C + 1) * δ := by
            exact mul_le_mul_of_nonneg_left h_compl_le (by positivity)
    have h_err_μ : ∀ n,
        |∫ ω, f ω ∂(μ (φ n)) - ∫ ω, g (configBasisEval ω) ∂(μ (φ n))| ≤
        2 * (C + 1) * δ := fun n => h_err_bound _ (hμ_prob (φ n)) (hK_mass (φ n))
    have h_err_ν :
        |∫ ω, f ω ∂ν - ∫ ω, g (configBasisEval ω) ∂ν| ≤
        2 * (C + 1) * δ := h_err_bound _ hν_prob hν_K_mass
    -- Combine: triangle inequality
    refine ⟨N, fun n hn => ?_⟩
    -- Set up abbreviations for readability
    set Iμn := ∫ ω, f ω ∂μ (φ n)
    set Iν := ∫ ω, f ω ∂ν
    set Gμn := ∫ ω, g (configBasisEval ω) ∂μ (φ n)
    set Gν := ∫ x, g x ∂ν_lim
    have hGν_eq : Gν = ∫ ω, g (configBasisEval ω) ∂ν := h_chvar_ν
    have hGμn_eq : ∀ m, ∫ x, g x ∂(Measure.map configBasisEval (μ (φ m))) =
        ∫ ω, g (configBasisEval ω) ∂(μ (φ m)) := h_chvar_μ
    -- The middle term is small
    have h_mid : |Gμn - Gν| < ε / 3 := by
      have := hN n hn
      rw [Real.dist_eq, hGμn_eq n] at this
      exact this
    calc dist Iμn Iν = |Iμn - Iν| := Real.dist_eq _ _
      _ = |(Iμn - Gμn) + (Gμn - Gν) + (Gν - Iν)| := by ring_nf
      _ ≤ |Iμn - Gμn| + |Gμn - Gν| + |Gν - Iν| := by
          have h1 := abs_add_le (Iμn - Gμn + (Gμn - Gν)) (Gν - Iν)
          have h2 := abs_add_le (Iμn - Gμn) (Gμn - Gν)
          linarith
      _ ≤ 2 * (C + 1) * δ + ε / 3 + 2 * (C + 1) * δ := by
          have h1 := h_err_μ n
          have h3 : |Gν - Iν| ≤ 2 * (C + 1) * δ := by
            rw [hGν_eq, abs_sub_comm]; exact h_err_ν
          linarith [h_mid.le]
      _ < ε := by rw [hδ_def]; field_simp; linarith
  · -- f is not strongly measurable → contradiction
    -- Every continuous f on Configuration E is measurable (hence strongly measurable)
    -- w.r.t. the cylindrical σ-algebra, using DM partial sum approximations.
    exfalso; apply hf_sm
    suffices Measurable f from this.stronglyMeasurable
    -- Approximate f by functions depending on finitely many DM coordinates:
    -- g_n(ω) = f(Σ_{m<n} ω(basis_m) • coeff_m)
    apply measurable_of_tendsto_metrizable
      (f := fun n (ω : Configuration E) => f ((Finset.range n).sum fun m =>
        ω (DyninMityaginSpace.basis m) • DyninMityaginSpace.coeff m))
    · -- Each g_n is measurable: factors as (continuous fn) ∘ configBasisEval
      intro n
      have h_eq : (fun ω : Configuration E => f ((Finset.range n).sum fun m =>
          ω (DyninMityaginSpace.basis m) • DyninMityaginSpace.coeff m)) =
        (fun x : ℕ → ℝ => f ((Finset.range n).sum fun m =>
          x m • DyninMityaginSpace.coeff (E := E) m)) ∘
        configBasisEval (E := E) := by ext ω; rfl
      rw [h_eq]
      exact (hf_cont.comp (continuous_finset_sum _ fun m _ =>
        (continuous_apply m).smul continuous_const)).measurable.comp
        configBasisEval_measurable
    · -- Pointwise convergence: g_n(ω) → f(ω) by DM expansion + continuity
      rw [tendsto_pi_nhds]; intro ω
      apply hf_cont.continuousAt.tendsto.comp
      -- π_n(ω) → ω in the weak-* topology on Configuration E
      rw [tendsto_iff_forall_eval_tendsto_topDualPairing]
      intro e; simp only [topDualPairing_apply]
      -- By DM expansion: ω(e) = Σ_m coeff_m(e) * ω(basis_m)
      have h := (DyninMityaginSpace.hasSum_basis (E := E) e).mapL (show E →L[ℝ] ℝ from ω)
      simp only [ContinuousLinearMap.map_smul, smul_eq_mul] at h
      -- Rewrite the CLM sum evaluation to match the DM HasSum
      have h_eq : ∀ n, ((Finset.range n).sum fun m =>
          ω (DyninMityaginSpace.basis m) • DyninMityaginSpace.coeff m) e =
        (Finset.range n).sum fun m =>
          (DyninMityaginSpace.coeff m) e * ω (DyninMityaginSpace.basis m) := by
        intro n; induction n with
        | zero => simp
        | succ n ih =>
          simp only [Finset.sum_range_succ, ContinuousLinearMap.add_apply, ih,
            ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm]
      exact (h.tendsto_sum_nat).congr (fun n => (h_eq n).symm)

end GaussianField
