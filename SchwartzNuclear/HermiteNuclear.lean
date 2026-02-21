/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DyninMityaginSpace Instance for Schwartz Space

Derives the `DyninMityaginSpace (SchwartzMap D ℝ)` instance from the topological
isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq` constructed in
`SchwartzNuclear.HermiteTensorProduct`.

## Main result

- `schwartz_dyninMityaginSpace`: the `DyninMityaginSpace` instance for Schwartz space
  on any nontrivial finite-dimensional real normed space.
-/

import SchwartzNuclear.HermiteTensorProduct

noncomputable section

open GaussianField

namespace GaussianField

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- **Schwartz space is a nuclear Fréchet space.**

The instance uses the Schwartz seminorm family `(k, l) ↦ p_{k,l}` and a
basis/coefficient system derived from the topological isomorphism
`SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

Proved via the topological isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`
constructed from multi-dimensional Hermite analysis. -/
noncomputable instance schwartz_dyninMityaginSpace [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
    (schwartz_withSeminorms ℝ D ℝ)
    (schwartzRapidDecayEquiv D)

end GaussianField
