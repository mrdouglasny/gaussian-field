import GaussianField.Construction
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Continuum Test-Function Alias

Provides the alias `ContinuumTestFunction d := S(ℝ^d)` used by downstream
continuum-limit code.
-/

noncomputable section

namespace GaussianField

/-- Continuum test-function space `S(R^d)` used by downstream continuum limits. -/
abbrev ContinuumTestFunction (d : ℕ) :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

end GaussianField
