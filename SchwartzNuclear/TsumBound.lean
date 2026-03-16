/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tsum bound helpers for nuclear extension
-/

import SchwartzNuclear.HermiteNuclear

noncomputable section

open GaussianField

namespace GaussianField

/-- If `|a_m| ≤ B * w_m` pointwise and both series converge, then `|Σ a_m| ≤ B * Σ w_m`.

Note: `norm_tsum_le_tsum_norm` for `ℕ → ℝ` exceeds 800k heartbeats.
The mathematical content is: `|Σ a_m| ≤ Σ |a_m| ≤ Σ B w_m = B Σ w_m`. -/
theorem abs_tsum_le_of_pointwise_le {a w : ℕ → ℝ} {B : ℝ}
    (ha : Summable a) (hw : Summable w) (_hB : 0 ≤ B)
    (h_pw : ∀ m, |a m| ≤ B * w m) :
    |∑' m, a m| ≤ B * ∑' m, w m := by
  have hBw_nonneg : ∀ m, 0 ≤ B * w m := fun m =>
    le_trans (abs_nonneg _) (h_pw m)
  have h_partial : ∀ N, abs ((Finset.range N).sum a) ≤ B * (∑' m, w m) := by
    intro N
    calc
      abs ((Finset.range N).sum a) ≤ (Finset.range N).sum fun m => |a m| := by
        simpa using (Finset.abs_sum_le_sum_abs (s := Finset.range N) (f := a))
      _ ≤ (Finset.range N).sum (fun m => B * w m) := by
        exact Finset.sum_le_sum fun m _ => h_pw m
      _ ≤ ∑' m, B * w m := by
        exact (hw.mul_left B).sum_le_tsum (Finset.range N) (fun m _ => hBw_nonneg m)
      _ = B * (∑' m, w m) := by
        rw [tsum_mul_left]
  have h_tendsto_abs :=
    continuous_abs.continuousAt.tendsto.comp ha.hasSum.tendsto_sum_nat
  exact le_of_tendsto h_tendsto_abs (Filter.Eventually.of_forall h_partial)

end GaussianField
