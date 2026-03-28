/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Laplace Transform as a CLM on Schwartz Space

Constructs the one-sided Laplace evaluation functional
  `L_ω(h) = ∫₀^∞ h(t) e^{-ωt} dt`
as a CLM `𝓢(ℝ) →L[ℝ] ℝ` for `ω > 0`, and proves a uniform Schwartz
seminorm bound for `ω ≥ mass > 0`.

## Main definitions

- `schwartzLaplaceEvalCLM ω hω` — the Laplace evaluation CLM

## Main results

- `schwartzLaplaceEvalCLM_apply` — specification: equals the one-sided integral
- `schwartzLaplace_uniformBound` — `|L_ω(h)| ≤ C · p(h)` uniformly in ω ≥ mass

## Proof strategy

The key bound is ω-independent: for h ∈ 𝓢(ℝ) and ω > 0,

  `|L_ω(h)| ≤ ∫₀^∞ |h(t)| dt ≤ ∫_ℝ |h(t)| dt = ‖h‖_{L¹}`

and Schwartz functions are in L¹ (by `SchwartzMap.integrable`).
For the explicit seminorm bound, `‖h‖_{L¹} ≤ C · p_{k,0}(h)` for k ≥ 2.

## References

- Reed-Simon II, §IX.3 (Schwartz space properties)
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open MeasureTheory Real Set Filter
open scoped BigOperators

namespace GaussianField

/-! ## Auxiliary bounds -/

/-- `‖exp(-ω·t)‖ ≤ 1` for `t ≥ 0` and `ω > 0`. -/
private lemma norm_exp_neg_mul_le_one (ω : ℝ) (hω : 0 < ω) (t : ℝ) (ht : 0 ≤ t) :
    ‖exp (-ω * t)‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

/-! ## Schwartz integrability -/

/-- Schwartz functions are integrable on `[0, ∞)` against `e^{-ωt}` for ω > 0.

Proof: `‖h(t) e^{-ωt}‖ ≤ ‖h(t)‖` since `‖e^{-ωt}‖ ≤ 1` for t ≥ 0, ω > 0.
And `‖h‖` is integrable by `SchwartzMap.integrable.norm`. -/
private lemma schwartz_integrable_exp_neg (f : SchwartzMap ℝ ℝ) (ω : ℝ) (hω : 0 < ω) :
    IntegrableOn (fun t => f.toFun t * exp (-ω * t)) (Ici 0) volume := by
  apply Integrable.mono' f.integrable.norm.integrableOn
  · have hc : Continuous (fun t => exp (-ω * t)) := by fun_prop
    exact (f.continuous.mul hc).aestronglyMeasurable.restrict
  · apply (ae_restrict_iff' measurableSet_Ici).mpr (ae_of_all _ fun t ht => ?_)
    simp only [norm_mul, mem_Ici] at *
    exact le_trans (mul_le_of_le_one_right (norm_nonneg _)
      (norm_exp_neg_mul_le_one ω hω t ht)) le_rfl

/-- The norm of the Laplace integral is bounded by `‖h‖_{L¹}`.

  `‖∫₀^∞ h(t)e^{-ωt} dt‖ ≤ ∫₀^∞ ‖h(t)‖ dt ≤ ∫_ℝ ‖h(t)‖ dt` -/
private lemma laplace_integral_le_l1_norm (f : SchwartzMap ℝ ℝ) (ω : ℝ) (hω : 0 < ω) :
    ‖∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)‖ ≤
    ∫ t, ‖f.toFun t‖ := by
  calc ‖∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)‖
      ≤ ∫ t in Ici (0 : ℝ), ‖f.toFun t * exp (-ω * t)‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ici (0 : ℝ), ‖f.toFun t‖ := by
        apply setIntegral_mono_on (schwartz_integrable_exp_neg f ω hω).norm
          f.integrable.norm.integrableOn measurableSet_Ici
        intro t ht
        simp only [norm_mul, mem_Ici] at *
        exact le_trans (mul_le_of_le_one_right (norm_nonneg _)
          (norm_exp_neg_mul_le_one ω hω t ht)) le_rfl
    _ ≤ ∫ t, ‖f.toFun t‖ :=
        setIntegral_le_integral f.integrable.norm
          (ae_of_all _ fun t => norm_nonneg _)

/-! ## Laplace evaluation CLM construction -/

/-- The Laplace evaluation as a linear map. -/
private def laplaceEvalLinear (ω : ℝ) (hω : 0 < ω) : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ where
  toFun f := ∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)
  map_add' f g := by
    show ∫ t in Ici (0 : ℝ), (f + g).toFun t * exp (-ω * t) = _
    have h : ∀ t, (f + g).toFun t * exp (-ω * t) =
      f.toFun t * exp (-ω * t) + g.toFun t * exp (-ω * t) :=
      fun t => by change (f + g) t * _ = _; simp [add_mul]; rfl
    simp_rw [h]
    exact integral_add (schwartz_integrable_exp_neg f ω hω)
      (schwartz_integrable_exp_neg g ω hω)
  map_smul' r f := by
    show ∫ t in Ici (0 : ℝ), (r • f).toFun t * exp (-ω * t) =
      r • ∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)
    have h : ∀ t, (r • f).toFun t * exp (-ω * t) =
      r • (f.toFun t * exp (-ω * t)) :=
      fun t => by
        show (r • f) t * exp (-ω * t) = r * (f.toFun t * exp (-ω * t))
        simp only [SchwartzMap.smul_apply, smul_eq_mul]
        have : f t = f.toFun t := rfl
        rw [this]; ring
    simp_rw [h, integral_smul]

/-- **The Laplace evaluation CLM on Schwartz space.**

  `L_ω(h) = ∫₀^∞ h(t) e^{-ωt} dt`

Continuity: `|L_ω(h)| ≤ ‖h‖_{L¹}` and the L¹ norm is continuous on 𝓢(ℝ). -/
def schwartzLaplaceEvalCLM (ω : ℝ) (hω : 0 < ω) : SchwartzMap ℝ ℝ →L[ℝ] ℝ where
  toLinearMap := laplaceEvalLinear ω hω
  cont := by
    -- Use WithSeminorms.continuous_of_isBounded: bound target seminorm by Schwartz seminorms.
    -- Chain: |L f| ≤ ‖toLp f‖ ≤ C · s.sup(p)(f) via toLpCLM + bound_of_continuous.
    apply (schwartz_withSeminorms ℝ ℝ ℝ).continuous_of_isBounded (norm_withSeminorms ℝ ℝ)
    intro i
    set T : SchwartzMap ℝ ℝ →L[ℝ] Lp ℝ 1 (volume : Measure ℝ) :=
      SchwartzMap.toLpCLM ℝ ℝ 1 (μ := volume)
    set qT : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
      (normSeminorm ℝ (Lp ℝ 1 (volume : Measure ℝ))).comp T.toLinearMap
    have hqT : Continuous qT := continuous_norm.comp T.continuous
    obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous
      (schwartz_withSeminorms ℝ ℝ ℝ) qT hqT
    refine ⟨s, C, fun f => le_trans ?_ (hle f)⟩
    -- ‖L f‖ ≤ ‖T f‖ (Laplace integral bounded by L¹ norm)
    show ‖(laplaceEvalLinear ω hω) f‖ ≤ ‖T f‖
    calc ‖(laplaceEvalLinear ω hω) f‖
        = ‖∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)‖ := rfl
      _ ≤ ∫ t, ‖f.toFun t‖ := laplace_integral_le_l1_norm f ω hω
      _ = ‖(T f : Lp ℝ 1 volume)‖ := by
          rw [SchwartzMap.toLpCLM_apply, L1.norm_eq_integral_norm]
          exact integral_congr_ae (by
            filter_upwards [f.coeFn_toLp 1 volume] with t ht
            simp only [Real.norm_eq_abs]; congr 1; exact ht.symm)

/-- **Specification of the Laplace evaluation CLM.** -/
theorem schwartzLaplaceEvalCLM_apply (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    schwartzLaplaceEvalCLM ω hω h =
    ∫ t in Ici (0 : ℝ), h.toFun t * exp (-ω * t) := rfl

/-- **Uniform Schwartz seminorm bound for the Laplace evaluation.**

For `ω ≥ mass > 0`, the bound `|L_ω(h)| ≤ C · p(h)` holds with constants
independent of ω, because `e^{-ωt} ≤ 1` for t ≥ 0, ω > 0. -/
theorem schwartzLaplace_uniformBound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (h : SchwartzMap ℝ ℝ),
      |schwartzLaplaceEvalCLM ω (lt_of_lt_of_le hmass hω) h| ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) h := by
  -- Get the L¹ norm bound on Schwartz seminorms via toLpCLM + bound_of_continuous
  set T : SchwartzMap ℝ ℝ →L[ℝ] Lp ℝ 1 (volume : Measure ℝ) :=
    SchwartzMap.toLpCLM ℝ ℝ 1 (μ := volume)
  set q : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
    Seminorm.comp (normSeminorm ℝ (Lp ℝ 1 (volume : Measure ℝ))) T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℝ) q hq
  refine ⟨s, C, lt_of_le_of_ne C.2 (fun h => hC (Subtype.ext h.symm)), fun ω hω h => ?_⟩
  rw [schwartzLaplaceEvalCLM_apply]
  -- |∫ h·e^{-ωt}| ≤ ‖∫ h·e^{-ωt}‖ ≤ ∫ ‖h‖ = ‖toLp h‖ = q h ≤ C · s.sup(p)(h)
  calc |∫ t in Ici (0 : ℝ), h.toFun t * exp (-ω * t)|
      = ‖∫ t in Ici (0 : ℝ), h.toFun t * exp (-ω * t)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ t, ‖h.toFun t‖ := laplace_integral_le_l1_norm h ω (lt_of_lt_of_le hmass hω)
    _ = ‖(T h : Lp ℝ 1 volume)‖ := by
        rw [SchwartzMap.toLpCLM_apply, L1.norm_eq_integral_norm]
        exact integral_congr_ae (by
          filter_upwards [h.coeFn_toLp 1 volume] with t ht
          simp only [Real.norm_eq_abs]; congr 1; exact ht.symm)
    _ = q h := rfl
    _ ≤ C * (s.sup (fun m => schwartzSeminormFamily ℝ ℝ ℝ m)) h := hle h

end GaussianField
