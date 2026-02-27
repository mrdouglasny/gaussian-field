/-
Copyright (c) 2026 Michael R. Douglas and Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Embedding: Discrete Lattice to Continuous Torus

Embeds the discrete torus `FinLatticeSites d N = (Fin d → ZMod N)` into the
continuous torus `(Fin d → AddCircle p)` via `ZMod.toAddCircle` and rescaling.

The framework for connecting ZMod-based lattice sites to AddCircle-based
continuous torus representations is due to Yoh Tanimoto.

## Main definitions

- `ContinuousTorus d p` — the continuous torus `(ℝ/pℤ)^d`
- `toScaledAddCircle` — `ZMod N →+ AddCircle p` for arbitrary period `p`
- `siteToTorus` — embedding `FinLatticeSites d N →+ ContinuousTorus d p`
- `siteToUnitTorus` — embedding into the unit torus `(ℝ/ℤ)^d`

## Mathematical background

The discrete torus (ℤ/Nℤ)^d embeds into the continuous torus (ℝ/pℤ)^d via
the map `x ↦ (i ↦ p·(x i)/N mod p)`. This is the composition of Mathlib's
`ZMod.toAddCircle : ZMod N →+ AddCircle 1` with the rescaling equivalence
`AddCircle.equivAddCircle : AddCircle 1 ≃+ AddCircle p`.

This embedding is key for:
- Defining the continuum limit (N → ∞ with the torus fixed)
- Multi-scale renormalization via `ZMod.castHom`
- Fourier analysis on the lattice via AddCircle's Fourier theory
-/

import Lattice.Sites
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Group.Pi.Lemmas

noncomputable section

namespace GaussianField

/-! ## Continuous torus -/

/-- The continuous d-dimensional torus with period `p`: the product `(ℝ/pℤ)^d`. -/
abbrev ContinuousTorus (d : ℕ) (p : ℝ) := Fin d → AddCircle p

/-! ## Scaled AddCircle embedding -/

/-- The `AddMonoidHom` from `ZMod N` to `AddCircle p`, sending `j mod N` to
`p·j/N mod p`. Constructed as the composition of `ZMod.toAddCircle` (to the
unit circle) with `AddCircle.equivAddCircle` (rescaling from period 1 to
period p). Due to Yoh Tanimoto. -/
noncomputable def ZMod.toScaledAddCircle (p : ℝ) (N : ℕ) [NeZero N]
    (hp : p ≠ 0) : ZMod N →+ AddCircle p :=
  (AddCircle.equivAddCircle 1 p one_ne_zero hp).toAddMonoidHom.comp ZMod.toAddCircle

lemma ZMod.toScaledAddCircle_injective (p : ℝ) (N : ℕ) [NeZero N] (hp : p ≠ 0) :
    Function.Injective (ZMod.toScaledAddCircle p N hp) :=
  (AddCircle.equivAddCircle 1 p one_ne_zero hp).injective.comp
    (ZMod.toAddCircle_injective N)

@[simp] lemma ZMod.toScaledAddCircle_inj (p : ℝ) {N : ℕ} [NeZero N]
    (hp : p ≠ 0) {j k : ZMod N} :
    ZMod.toScaledAddCircle p N hp j = ZMod.toScaledAddCircle p N hp k ↔ j = k :=
  (ZMod.toScaledAddCircle_injective p N hp).eq_iff

@[simp] lemma ZMod.toScaledAddCircle_eq_zero (p : ℝ) {N : ℕ} [NeZero N]
    (hp : p ≠ 0) {j : ZMod N} :
    ZMod.toScaledAddCircle p N hp j = 0 ↔ j = 0 :=
  map_eq_zero_iff _ (ZMod.toScaledAddCircle_injective p N hp)

/-! ## Torus embedding maps -/

/-- Embed the discrete torus `(ℤ/Nℤ)^d` into the unit continuous torus `(ℝ/ℤ)^d`
via Mathlib's `ZMod.toAddCircle`. Site `x` maps to `(i ↦ (x i)/N mod 1)`. -/
noncomputable def siteToUnitTorus (d N : ℕ) [NeZero N] :
    FinLatticeSites d N →+ ContinuousTorus d 1 :=
  Pi.addMonoidHom (fun _ => ZMod.toAddCircle)

/-- The unit torus embedding is injective. -/
theorem siteToUnitTorus_injective (d N : ℕ) [NeZero N] :
    Function.Injective (siteToUnitTorus d N) :=
  Pi.addMonoidHom_injective _ (fun _ => ZMod.toAddCircle_injective N)

/-- Embed the discrete torus `(ℤ/Nℤ)^d` into the continuous torus `(ℝ/pℤ)^d`.
Sends lattice site `x` to `(i ↦ p·(x i)/N mod p)`. -/
noncomputable def siteToTorus (d N : ℕ) [NeZero N] (p : ℝ) (hp : p ≠ 0) :
    FinLatticeSites d N →+ ContinuousTorus d p :=
  Pi.addMonoidHom (fun _ => ZMod.toScaledAddCircle p N hp)

/-- The scaled torus embedding is injective. -/
theorem siteToTorus_injective (d N : ℕ) [NeZero N] (p : ℝ) (hp : p ≠ 0) :
    Function.Injective (siteToTorus d N p hp) :=
  Pi.addMonoidHom_injective _ (fun _ => ZMod.toScaledAddCircle_injective p N hp)

/-- The scaled torus embedding relates to the unit embedding via rescaling. -/
theorem siteToTorus_eq_equivAddCircle_comp (d N : ℕ) [NeZero N] (p : ℝ)
    (hp : p ≠ 0) (x : FinLatticeSites d N) (i : Fin d) :
    siteToTorus d N p hp x i =
    AddCircle.equivAddCircle 1 p one_ne_zero hp (siteToUnitTorus d N x i) := by
  simp [siteToTorus, siteToUnitTorus, ZMod.toScaledAddCircle]

end GaussianField
