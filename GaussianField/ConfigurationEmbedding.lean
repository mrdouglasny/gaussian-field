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

One sorry remains:
- `prokhorov_configuration` (pullback steps): pulling back the limit measure
  from ℕ → ℝ to Configuration E via `Measure.comap`.

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

noncomputable section

namespace GaussianField

open MeasureTheory Filter BoundedContinuousFunction
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
    congr 1; ext m; rw [hbasis m]

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
- `prokhorov_configuration`: pulls back to Configuration E (sorry for weak
  convergence transfer, which requires Tietze extension). -/

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
          · push_neg at h
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

**Sorry**: The weak convergence transfer from ℕ → ℝ back to Configuration E
requires showing that bounded continuous functions on Configuration E
extend to bounded continuous functions on ℕ → ℝ (Tietze-type extension).
Use `prokhorov_configuration_pushforward` for a fully proved version. -/
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
  -- The pullback measure is well-defined via Measure.comap (injectivity + null-measurability
  -- from concentration on range). The remaining sorry is the weak convergence transfer:
  -- showing that bounded continuous functions on Configuration E can be tested against
  -- the pullback measure via extension to ℕ → ℝ.
  sorry

end GaussianField
