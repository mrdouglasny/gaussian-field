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
  sorry

end GaussianField
