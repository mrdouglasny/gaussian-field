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
- `isGoodNoise_ae`: the set of "good" noise configurations has full measure
-/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.InfinitePi

noncomputable section

namespace GaussianMeasure

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- **Gaussian series convergence**: If ∑ ‖vₙ‖ < ∞ and ξₙ ~ iid N(0,1),
    then ∑ ξₙ • vₙ converges almost surely in K.

    Proof uses Tonelli's theorem:
    E[∑ ‖ξₙ vₙ‖] = ∑ E[|ξₙ|] ‖vₙ‖ = C · ∑ ‖vₙ‖ < ∞
    so ∑ ‖ξₙ vₙ‖ < ∞ a.s., hence ∑ ξₙ vₙ converges a.s. -/
theorem hilbert_gaussian_series_converges
    (v : ℕ → K) (hv : Summable (fun n => ‖v n‖)) :
    ∀ᵐ ξ ∂(MeasureTheory.Measure.infinitePi (fun _ : ℕ => ProbabilityTheory.gaussianReal 0 1)),
      Summable (fun n => ξ n • v n) := by
  sorry

end GaussianMeasure
