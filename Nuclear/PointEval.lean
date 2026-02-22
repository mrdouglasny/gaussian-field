/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HasPointEval — Pointwise Evaluation Typeclass

Defines `HasPointEval E M`, a typeclass asserting that elements of `E`
can be evaluated at points of `M` to produce real numbers. This captures
the common pattern across Schwartz functions, smooth periodic functions,
nuclear tensor products, and finite-dimensional function spaces.

## Main definitions

- `HasPointEval E M` — typeclass with `pointEval : E → M → ℝ`
- Instances for `SchwartzMap`, `SmoothMap_Circle`, `NuclearTensorProduct`, `Fin N → ℝ`
-/

import Nuclear.NuclearTensorProduct
import SmoothCircle.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

noncomputable section

namespace GaussianField

/-- Typeclass for spaces whose elements can be evaluated at points.

This abstracts the common pattern: Schwartz functions evaluate at points of ℝᵈ,
smooth periodic functions evaluate at points of ℝ, tensor products evaluate at
pairs, and lattice fields evaluate at lattice sites. -/
class HasPointEval (E : Type*) (M : outParam Type*) where
  pointEval : E → M → ℝ

namespace HasPointEval

/-- Evaluate an element at a point. -/
def eval {E M : Type*} [HasPointEval E M] (f : E) (x : M) : ℝ :=
  pointEval f x

end HasPointEval

/-! ## Instances -/

/-- Schwartz functions on a normed space can be evaluated pointwise. -/
instance schwartz_hasPointEval (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [MeasurableSpace D] :
    HasPointEval (SchwartzMap D ℝ) D where
  pointEval f x := f x

/-- Smooth periodic functions on S¹_L can be evaluated at points of ℝ. -/
instance smoothCircle_hasPointEval (L : ℝ) [Fact (0 < L)] :
    HasPointEval (SmoothMap_Circle L ℝ) ℝ where
  pointEval f x := f.toFun x

/-- Nuclear tensor products inherit pointwise evaluation via Cantor pairing.
Elements are rapid-decay sequences; evaluation at index m gives the m-th coefficient. -/
instance nuclearTensorProduct_hasPointEval (E₁ E₂ : Type*) :
    HasPointEval (NuclearTensorProduct E₁ E₂) ℕ where
  pointEval a m := a.val m

/-- Finite-dimensional function spaces ℝᴺ evaluate at indices. -/
instance fin_hasPointEval (N : ℕ) :
    HasPointEval (Fin N → ℝ) (Fin N) where
  pointEval f i := f i

end GaussianField
