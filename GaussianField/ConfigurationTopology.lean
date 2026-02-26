import GaussianField.Construction
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Metrizable.Basic

/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Topology and Measurability on Configuration Space

Provides topological/measurable structure declarations for
`Configuration (ContinuumTestFunction d) = S'(R^d)`.

These declarations are used by downstream projects (e.g. pphi2) for
Prokhorov/tightness arguments on continuum limits.
-/

noncomputable section

namespace GaussianField

/-- Continuum test-function space `S(R^d)` used by downstream continuum limits. -/
abbrev ContinuumTestFunction (d : ℕ) :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

/-- `S'(R^d) = Configuration (ContinuumTestFunction d)` is a Polish space. -/
axiom configuration_polishSpace (d : ℕ) :
    PolishSpace (Configuration (ContinuumTestFunction d))

/-- Borel measurable structure on `S'(R^d)`. -/
axiom configuration_borelSpace (d : ℕ) :
    BorelSpace (Configuration (ContinuumTestFunction d))

end GaussianField
