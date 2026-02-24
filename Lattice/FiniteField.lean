/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite Lattice Field Space

Defines the field space on the finite lattice (discrete torus) as
`FinLatticeSites d N → ℝ`. This is a finite-dimensional vector space
with a natural DyninMityaginSpace instance via delta-function basis.

## Main definitions

- `FinLatticeField d N` — field configuration space on the finite lattice
- `DyninMityaginSpace` instance — finite-dimensional (delta basis)
- `HasPointEval` instance — evaluation at lattice sites
-/

import Lattice.Sites
import Nuclear.DyninMityagin
import Nuclear.NuclearTensorProduct
import Nuclear.PointEval
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.LinearAlgebra.Dimension.Finrank

noncomputable section

namespace GaussianField

/-! ## Field space -/

/-- Field configuration on the finite lattice: a real-valued function on
the discrete torus (ℤ/Nℤ)^d. -/
abbrev FinLatticeField (d : ℕ) (N : ℕ) := FinLatticeSites d N → ℝ

/-! ## HasPointEval instance -/

/-- Finite lattice fields can be evaluated at lattice sites. -/
instance finLatticeField_hasPointEval (d N : ℕ) :
    HasPointEval (FinLatticeField d N) (FinLatticeSites d N) where
  pointEval f x := f x

/-! ## DyninMityaginSpace instance

The finite-dimensional case: `FinLatticeField d N ≅ ℝ^(N^d)` is trivially
nuclear. We construct the DyninMityaginSpace instance using delta functions
as basis and point evaluations as coefficients.

For indices beyond the number of lattice sites, basis vectors are zero.
This means rapid decay holds trivially (eventually-zero sequences). -/

variable (d N : ℕ) [NeZero N]

/-- Enumeration of finite lattice sites via Fintype. -/
private noncomputable def finLatticeSiteEnum :
    FinLatticeSites d N ≃ Fin (Fintype.card (FinLatticeSites d N)) :=
  Fintype.equivFin _

/-- Delta function at a lattice site. -/
def finLatticeDelta (x : FinLatticeSites d N) : FinLatticeField d N :=
  fun y => if y = x then 1 else 0

/-- The m-th basis vector: delta function at the m-th site (or zero if m ≥ |sites|). -/
def finLatticeBasisVec (m : ℕ) : FinLatticeField d N :=
  if h : m < Fintype.card (FinLatticeSites d N) then
    finLatticeDelta d N ((finLatticeSiteEnum d N).symm ⟨m, h⟩)
  else 0

/-- The m-th coefficient: evaluation at the m-th site (or zero if m ≥ |sites|). -/
def finLatticeCoeffCLM (m : ℕ) : FinLatticeField d N →L[ℝ] ℝ :=
  if h : m < Fintype.card (FinLatticeSites d N) then
    { toLinearMap :=
      { toFun := fun f => f ((finLatticeSiteEnum d N).symm ⟨m, h⟩)
        map_add' := fun _ _ => rfl
        map_smul' := fun r f => by simp [smul_eq_mul] }
      cont := continuous_apply _ }
  else 0

/-- The sup-norm seminorm on the finite lattice field. -/
def finLatticeSeminorm : Seminorm ℝ (FinLatticeField d N) where
  toFun f := Finset.univ.sup' Finset.univ_nonempty (fun x => ‖f x‖₊)
  map_zero' := by simp
  add_le' f g := by
    sorry
  neg' f := by simp [Pi.neg_apply, nnnorm_neg]
  smul' r f := by
    sorry

/-- The DyninMityaginSpace instance for finite lattice fields.

Uses delta functions as basis, point evaluations as coefficients.
The expansion is the identity `f = ∑_x f(x) · δ_x`.
Basis growth and coefficient decay are trivial: beyond the N^d-th index,
everything is zero. -/
noncomputable instance finLatticeField_dyninMityaginSpace :
    DyninMityaginSpace (FinLatticeField d N) where
  ι := Unit
  p := fun _ => finLatticeSeminorm d N
  h_with := sorry -- WithSeminorms for the product topology
  basis := finLatticeBasisVec d N
  coeff := finLatticeCoeffCLM d N
  expansion := sorry -- f = ∑_x f(x) · δ_x (finite sum, standard linear algebra)
  basis_growth := fun _ => ⟨1, one_pos, 0, fun m => by
    simp only [pow_zero, mul_one]
    by_cases h : m < Fintype.card (FinLatticeSites d N)
    · -- Basis vector is a delta function, sup norm = 1
      sorry
    · -- Beyond range: basis vector is zero, seminorm = 0
      sorry⟩
  coeff_decay := fun k => ⟨1, one_pos, {()}, fun f m => by
    simp only [Finset.sup_singleton]
    by_cases h : m < Fintype.card (FinLatticeSites d N)
    · -- |coeff m f| ≤ sup_x |f(x)| ≤ finLatticeSeminorm f
      sorry
    · -- Beyond range: coeff is zero
      sorry⟩

end GaussianField
