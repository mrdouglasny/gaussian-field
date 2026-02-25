/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Sites — Types and Geometry

Defines lattice site types for both finite (periodic boundary conditions)
and infinite lattices, along with nearest-neighbor structure and ℓ¹ norm.

## Main definitions

- `FinLatticeSites d N` — sites of the discrete torus (ℤ/Nℤ)^d
- `InfLatticeSites d` — sites of ℤ^d
- `latticeNorm` — ℓ¹ norm on ℤ^d
- `neighbors` — nearest neighbors on ℤ^d
- `neighborsFinite` — nearest neighbors with periodic BC
-/

import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Real.Basic

noncomputable section

namespace GaussianField

/-! ## Site types -/

/-- Finite lattice sites: the discrete torus (ℤ/Nℤ)^d with periodic BC. -/
abbrev FinLatticeSites (d : ℕ) (N : ℕ) := Fin d → Fin N

/-- Infinite lattice sites: ℤ^d. -/
abbrev InfLatticeSites (d : ℕ) := Fin d → ℤ

/-! ## ℓ¹ norm on ℤ^d -/

/-- The ℓ¹ norm on ℤ^d: `∑ i, |x i|`. Used as weight in rapid-decay seminorms. -/
def latticeNorm {d : ℕ} (x : Fin d → ℤ) : ℝ :=
  ∑ i : Fin d, |(x i : ℝ)|

theorem latticeNorm_nonneg {d : ℕ} (x : Fin d → ℤ) : 0 ≤ latticeNorm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem latticeNorm_zero {d : ℕ} : latticeNorm (fun _ : Fin d => (0 : ℤ)) = 0 := by
  simp [latticeNorm]

theorem latticeNorm_triangle {d : ℕ} (x y : Fin d → ℤ) :
    latticeNorm (fun i => x i + y i) ≤ latticeNorm x + latticeNorm y := by
  simp only [latticeNorm]
  calc ∑ i : Fin d, |(↑(x i + y i) : ℝ)|
      = ∑ i : Fin d, |(↑(x i) : ℝ) + ↑(y i)| := by
        congr 1; ext i; push_cast; ring_nf
    _ ≤ ∑ i : Fin d, (|(↑(x i) : ℝ)| + |(↑(y i) : ℝ)|) :=
        Finset.sum_le_sum fun i _ => abs_add_le _ _
    _ = (∑ i, |(↑(x i) : ℝ)|) + (∑ i, |(↑(y i) : ℝ)|) := Finset.sum_add_distrib

/-! ## Standard basis vectors in ℤ^d -/

/-- The i-th standard basis vector in ℤ^d. -/
def stdBasisInt (d : ℕ) (i : Fin d) : Fin d → ℤ :=
  fun j => if j = i then 1 else 0

/-- The norm of a standard basis vector is 1. -/
theorem latticeNorm_stdBasis {d : ℕ} (i : Fin d) :
    latticeNorm (stdBasisInt d i) = 1 := by
  simp only [latticeNorm, stdBasisInt]
  calc ∑ j : Fin d, |(↑(if j = i then (1 : ℤ) else 0) : ℝ)|
      = ∑ j : Fin d, if j = i then 1 else 0 := by
        congr 1; ext j; split_ifs <;> simp
    _ = 1 := by simp [Finset.sum_ite_eq']

/-- Shifting by +eᵢ changes the norm by at most 1. -/
theorem latticeNorm_shift_le {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    latticeNorm (fun j => x j + stdBasisInt d i j) ≤ latticeNorm x + 1 := by
  calc latticeNorm (fun j => x j + stdBasisInt d i j)
      ≤ latticeNorm x + latticeNorm (stdBasisInt d i) :=
        latticeNorm_triangle x (stdBasisInt d i)
    _ = latticeNorm x + 1 := by rw [latticeNorm_stdBasis]

/-- Shifting by -eᵢ changes the norm by at most 1. -/
theorem latticeNorm_shift_sub_le {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    latticeNorm (fun j => x j - stdBasisInt d i j) ≤ latticeNorm x + 1 := by
  have : (fun j => x j - stdBasisInt d i j) = (fun j => x j + (-stdBasisInt d i j)) := by
    ext j; ring
  rw [this]
  calc latticeNorm (fun j => x j + (-stdBasisInt d i j))
      ≤ latticeNorm x + latticeNorm (fun j => -stdBasisInt d i j) :=
        latticeNorm_triangle x (fun j => -stdBasisInt d i j)
    _ = latticeNorm x + latticeNorm (stdBasisInt d i) := by
        congr 1; simp only [latticeNorm]; congr 1; ext j
        push_cast; rw [abs_neg]
    _ = latticeNorm x + 1 := by rw [latticeNorm_stdBasis]

/-! ## Nearest neighbors -/

/-- Nearest neighbors of x on ℤ^d: the 2d points {x ± eᵢ : i = 1..d}. -/
def neighbors (d : ℕ) (x : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Finset.univ.biUnion fun i =>
    {fun j => x j + stdBasisInt d i j,
     fun j => x j - stdBasisInt d i j}

/-- Nearest neighbors on the finite lattice with periodic BC.
    Addition is modulo N in each coordinate. -/
def neighborsFinite (d N : ℕ) [NeZero N] (x : Fin d → Fin N) :
    Finset (Fin d → Fin N) :=
  Finset.univ.biUnion fun i =>
    {fun j => if j = i then x j + 1 else x j,
     fun j => if j = i then x j - 1 else x j}

/-! ## Cardinality -/

/-- The number of neighbors is at most 2d. -/
theorem neighbors_card_le (d : ℕ) (x : Fin d → ℤ) :
    (neighbors d x).card ≤ 2 * d := by
  unfold neighbors
  calc (Finset.univ.biUnion _).card
      ≤ ∑ _i ∈ Finset.univ, ({fun j => x j + stdBasisInt d _i j,
          fun j => x j - stdBasisInt d _i j} : Finset _).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin d, 2 := by
        apply Finset.sum_le_sum; intro i _
        exact le_of_le_of_eq (Finset.card_insert_le _ _) (by simp)
    _ = 2 * d := by simp [Finset.sum_const, mul_comm]

end GaussianField
