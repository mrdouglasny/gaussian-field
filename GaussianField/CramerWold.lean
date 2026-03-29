/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Cramér-Wold Theorem

The Cramér-Wold theorem states that two probability measures on a finite product `ι → ℝ`
are equal if they assign the same distribution to every linear functional `x ↦ ∑ i, c i * x i`.

## Proof

1. Every CLM `(ι → ℝ) →L[ℝ] ℝ` acts as `x ↦ ∑ i, c i * x i` for `c i = L (Pi.single i 1)`,
   by the decomposition `x = ∑ i, x i • Pi.single i 1` (`pi_eq_sum_univ'`) and linearity.
2. `charFun_map_eq_charFunDual_smul` gives `charFunDual ν L = charFun (ν.map ⇑L) 1`.
3. Equal pushforwards → equal `charFunDual` → equal measures (by `ext_of_charFunDual`).
-/

namespace GaussianField

open MeasureTheory Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cramér-Wold theorem**: Two probability measures on a finite product `ι → ℝ` are equal
    if they assign the same distribution to every linear functional `x ↦ ∑ i, c i * x i`. -/
theorem cramerWold
    (ν₁ ν₂ : Measure (ι → ℝ))
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ c : ι → ℝ,
      ν₁.map (fun x => ∑ i : ι, c i * x i) =
      ν₂.map (fun x => ∑ i : ι, c i * x i)) :
    ν₁ = ν₂ := by
  -- Step 1: The hypothesis covers all continuous linear functionals on ι → ℝ.
  -- Every L : (ι → ℝ) →L[ℝ] ℝ satisfies L x = ∑ i, L(eᵢ) * x i.
  have hmap : ∀ L : (ι → ℝ) →L[ℝ] ℝ, ν₁.map ⇑L = ν₂.map ⇑L := by
    intro L
    have hL : (⇑L : (ι → ℝ) → ℝ) = fun x => ∑ i : ι, L (Pi.single i 1) * x i := by
      ext x
      conv_lhs => rw [pi_eq_sum_univ' x]
      rw [map_sum]
      congr 1; ext i
      rw [map_smul, smul_eq_mul, mul_comm]
    rw [hL]
    exact h _
  -- Step 2: Equal pushforwards → equal charFunDual → equal measures.
  apply Measure.ext_of_charFunDual
  ext L
  rw [show charFunDual ν₁ L = charFun (ν₁.map ⇑L) 1 from by
        rw [charFun_map_eq_charFunDual_smul, one_smul],
      show charFunDual ν₂ L = charFun (ν₂.map ⇑L) 1 from by
        rw [charFun_map_eq_charFunDual_smul, one_smul],
      hmap L]

end GaussianField
