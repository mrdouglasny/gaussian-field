/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Series Convergence

If {vₙ} is a sequence in a Hilbert space K with ∑ ‖vₙ‖ < ∞ and
{ξₙ} are iid N(0,1), then ∑ ξₙ vₙ converges a.s. in K.

This is the key probabilistic ingredient: nuclear summability of the
factorization vectors guarantees a.s. convergence of the Gaussian series.

## Main results

- `hilbert_gaussian_series_converges`: a.e. convergence of ∑ ξₙ vₙ

## Proof technique

By Tonelli's theorem:
  E[∑ₙ |ξₙ| ‖vₙ‖] = ∑ₙ E[|ξₙ|] ‖vₙ‖ = √(2/π) · ∑ₙ ‖vₙ‖ < ∞
so ∑ₙ |ξₙ| ‖vₙ‖ < ∞ a.e., giving absolute convergence.

## References

- Gel'fand, Vilenkin, "Generalized Functions" Vol 4, Ch 3-4
- Fernique, "Processus linéaires, processus généralisés", Ann. Inst. Fourier 1967
- Durrett, "Probability: Theory and Examples", Thm 2.5.8 (Kolmogorov two-series)
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

set_option maxHeartbeats 1600000 in
/-- **Gaussian series convergence**: If ∑ ‖vₙ‖ < ∞ and ξₙ ~ iid N(0,1),
    then ∑ ξₙ • vₙ converges almost surely in K.

    Proof uses Tonelli's theorem:
    E[∑ ‖ξₙ vₙ‖] = ∑ E[|ξₙ|] ‖vₙ‖ = C · ∑ ‖vₙ‖ < ∞
    so ∑ ‖ξₙ vₙ‖ < ∞ a.s., hence ∑ ξₙ vₙ converges a.s. -/
theorem hilbert_gaussian_series_converges
    (v : ℕ → K) (hv : Summable (fun n => ‖v n‖)) :
    ∀ᵐ ξ ∂(Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)),
      Summable (fun n => ξ n • v n) := by
  set μ := fun _ : ℕ => gaussianReal (0 : ℝ) 1
  set P := Measure.infinitePi μ
  -- The first absolute moment C = E[|ξ|] of standard Gaussian is finite
  set C := ∫⁻ x : ℝ, ↑‖x‖₊ ∂(μ 0) with hC_def
  have hC : C ≠ ⊤ := by
    have h := (IsGaussian.integrable_dual (μ 0)
      (ContinuousLinearMap.id ℝ ℝ)).hasFiniteIntegral
    rw [hasFiniteIntegral_def] at h
    simp only [ContinuousLinearMap.id_apply, enorm_eq_nnnorm] at h
    exact h.ne
  -- Convert ∑ ‖vₙ‖ < ∞ to NNReal and ENNReal summability
  have hv_nn : Summable (fun n => ‖v n‖₊) := by
    have h1 : (fun n => (‖v n‖₊ : ℝ)) = fun n => ‖v n‖ := funext fun n => coe_nnnorm (v n)
    exact NNReal.summable_coe.mp (h1 ▸ hv)
  have hv_ennreal : tsum (fun n => ((‖v n‖₊ : NNReal) : ENNReal)) ≠ ⊤ :=
    ENNReal.tsum_coe_ne_top_iff_summable.mpr hv_nn
  -- Measurability of each summand ‖ξ n‖₊ * ‖v n‖₊
  have h_meas_f : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal)) :=
    fun n => (measurable_pi_apply n).nnnorm.coe_nnreal_ennreal
  have h_meas : ∀ n, Measurable (fun ξ : ℕ → ℝ => (‖ξ n‖₊ : ENNReal) * ‖v n‖₊) :=
    fun n => (h_meas_f n).mul_const _
  -- Each marginal integral equals C (by measure-preserving projection)
  have h_eval : ∀ n, ∫⁻ ξ, (‖ξ n‖₊ : ENNReal) ∂P = C := fun n =>
    (measurePreserving_eval_infinitePi μ n).lintegral_comp
      measurable_nnnorm.coe_nnreal_ennreal
  -- Main estimate: E[∑ |ξₙ| ‖vₙ‖] = C · ∑ ‖vₙ‖ < ∞
  have h_finite : ∫⁻ ξ, ∑' n, ((‖ξ n‖₊ : ENNReal) * ‖v n‖₊) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun n => (h_meas n).aemeasurable)]
    simp_rw [lintegral_mul_const _ (h_meas_f _), h_eval, ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top hC hv_ennreal
  -- A.e. finiteness from finite lintegral
  have h_ae := ae_lt_top (Measurable.ennreal_tsum h_meas) h_finite
  -- Convert ∑ ‖ξₙ‖₊ * ‖vₙ‖₊ < ⊤ to Summable (fun n => ξ n • v n)
  exact h_ae.mono fun ξ hξ => by
    simp_rw [← ENNReal.coe_mul] at hξ
    have hξ' : Summable (fun n => ‖ξ n‖₊ * ‖v n‖₊) :=
      ENNReal.tsum_coe_ne_top_iff_summable.mp hξ.ne
    have hξ'' : Summable (fun n => ‖ξ n • v n‖) := by
      refine (NNReal.summable_coe.mpr hξ').congr fun n => ?_
      rw [NNReal.coe_mul, coe_nnnorm, coe_nnnorm, norm_smul]
    exact hξ''.of_norm

end GaussianField
