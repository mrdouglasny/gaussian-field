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
    apply Finset.sup'_le _ _ (fun x hx => ?_)
    calc (↑‖(f + g) x‖₊ : ℝ)
        ≤ ↑‖f x‖₊ + ↑‖g x‖₊ := by exact_mod_cast nnnorm_add_le (f x) (g x)
      _ ≤ _ := add_le_add
          (Finset.le_sup' (fun y => (↑‖f y‖₊ : ℝ)) hx)
          (Finset.le_sup' (fun y => (↑‖g y‖₊ : ℝ)) hx)
  neg' f := by simp [Pi.neg_apply, nnnorm_neg]
  smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, nnnorm_mul, NNReal.coe_mul]
    simp only [show (↑‖r‖₊ : ℝ) = ‖r‖ from rfl]
    have := Finset.comp_sup'_eq_sup'_comp (s := Finset.univ)
      Finset.univ_nonempty (f := fun x => (↑‖f x‖₊ : ℝ)) (g := (‖r‖ * ·))
      (fun _ _ => mul_max_of_nonneg _ _ (norm_nonneg r))
    simp only [Function.comp] at this
    exact this.symm

/-- The DyninMityaginSpace instance for finite lattice fields.

Uses delta functions as basis, point evaluations as coefficients.
The expansion is the identity `f = ∑_x f(x) · δ_x`.
Basis growth and coefficient decay are trivial: beyond the N^d-th index,
everything is zero. -/
noncomputable instance finLatticeField_dyninMityaginSpace :
    DyninMityaginSpace (FinLatticeField d N) where
  ι := Unit
  p := fun _ => finLatticeSeminorm d N
  h_with := by
    rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf]
    simp only [iInf_const]
    have hfun : ⇑(finLatticeSeminorm d N) = (norm : FinLatticeField d N → ℝ) := by
      ext f; unfold finLatticeSeminorm
      change (Finset.univ.sup' Finset.univ_nonempty fun x => (↑‖f x‖₊ : ℝ)) = ‖f‖
      rw [Pi.norm_def]
      -- Step 1: pull coercion out of sup'
      have h1 : Finset.univ.sup' Finset.univ_nonempty (fun x : FinLatticeSites d N => (↑‖f x‖₊ : ℝ)) =
          ↑(Finset.univ.sup' Finset.univ_nonempty (fun x : FinLatticeSites d N => ‖f x‖₊)) :=
        (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty
          (g := NNReal.toReal)
          (fun a b => NNReal.coe_mono.map_sup a b)).symm
      rw [h1]
      -- Step 2: sup' = sup for NNReal (has OrderBot)
      exact congrArg NNReal.toReal
        (Finset.sup'_eq_sup Finset.univ_nonempty (fun x : FinLatticeSites d N => ‖f x‖₊))
    rw [hfun, comap_norm_nhds_zero]
  basis := finLatticeBasisVec d N
  coeff := finLatticeCoeffCLM d N
  expansion := fun φ f => by
    set C := Fintype.card (FinLatticeSites d N) with hC_def
    -- Terms vanish for m ≥ card
    have hvanish : ∀ m, ¬(m < C) →
        (finLatticeCoeffCLM d N m) f * φ (finLatticeBasisVec d N m) = 0 := by
      intro m hm
      unfold finLatticeCoeffCLM finLatticeBasisVec
      simp only [show ¬(m < Fintype.card (FinLatticeSites d N)) from hm, dite_false,
        ContinuousLinearMap.zero_apply, map_zero, mul_zero]
    -- Convert tprod to finite sum
    rw [tsum_eq_sum (s := Finset.range C) (fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      exact hvanish m (not_lt.mpr hm))]
    -- Rewrite the sum: ∑ coeff(m,f) * φ(basis m) = φ(∑ coeff(m,f) • basis m)
    have : ∀ m ∈ Finset.range C,
        (finLatticeCoeffCLM d N m) f * φ (finLatticeBasisVec d N m) =
        φ ((finLatticeCoeffCLM d N m) f • finLatticeBasisVec d N m) := by
      intro m _
      rw [map_smul, smul_eq_mul]
    rw [Finset.sum_congr rfl this, ← map_sum]
    congr 1
    -- Show f = ∑_{m < card} coeff(m,f) • basis(m)
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- The site x has some index m < card
    obtain ⟨⟨m, hm⟩, rfl⟩ := (finLatticeSiteEnum d N).symm.surjective x
    have hmain : (Finset.range C).sum
        (fun b => (finLatticeCoeffCLM d N b) f *
          finLatticeBasisVec d N b ((finLatticeSiteEnum d N).symm ⟨m, hm⟩)) =
        (finLatticeCoeffCLM d N m) f *
          finLatticeBasisVec d N m ((finLatticeSiteEnum d N).symm ⟨m, hm⟩) := by
      apply Finset.sum_eq_single
      · intro b hb hbm
        have hblt : b < Fintype.card (FinLatticeSites d N) := Finset.mem_range.mp hb
        simp only [finLatticeBasisVec, finLatticeDelta, hblt, dite_true]
        rw [if_neg]
        · ring
        · intro heq
          exact hbm ((Fin.val_eq_of_eq ((finLatticeSiteEnum d N).symm.injective heq)).symm)
      · intro hm'
        exact absurd (Finset.mem_range.mpr hm) hm'
    rw [hmain]
    have hm' : m < N ^ d := by rwa [show Fintype.card (FinLatticeSites d N) = N ^ d from by simp] at hm
    simp [finLatticeCoeffCLM, finLatticeBasisVec, finLatticeDelta, hm']
  basis_growth := fun _ => ⟨1, one_pos, 0, fun m => by
    simp only [pow_zero, mul_one]
    unfold finLatticeSeminorm finLatticeBasisVec
    by_cases h : m < Fintype.card (FinLatticeSites d N)
    · simp only [h, dite_true]
      apply Finset.sup'_le Finset.univ_nonempty
      intro x _
      simp only [finLatticeDelta]
      split_ifs with heq
      · simp
      · simp
    · simp only [h, dite_false]
      simp⟩
  coeff_decay := fun k => ⟨(1 + Fintype.card (FinLatticeSites d N) : ℝ) ^ k,
    by positivity, {()}, fun f m => by
    simp only [Finset.sup_singleton]
    unfold finLatticeCoeffCLM finLatticeSeminorm
    by_cases h : m < Fintype.card (FinLatticeSites d N)
    · simp only [h, dite_true, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      set y := (finLatticeSiteEnum d N).symm ⟨m, h⟩
      set sem := Finset.univ.sup' Finset.univ_nonempty (fun x => (↑‖f x‖₊ : ℝ)) with sem_def
      have hnorm_le : (↑‖f y‖₊ : ℝ) ≤ sem :=
        Finset.le_sup' (fun x => (↑‖f x‖₊ : ℝ)) (Finset.mem_univ y)
      have hcoeff : |f y| ≤ sem := by
        calc |f y| = ‖f y‖ := (Real.norm_eq_abs _).symm
          _ ≤ sem := by exact_mod_cast hnorm_le
      have hpow : (1 + (m : ℝ)) ^ k ≤
          (1 + (Fintype.card (FinLatticeSites d N) : ℝ)) ^ k := by gcongr
      have hsem_nn : 0 ≤ sem := le_trans (by positivity) hnorm_le
      calc |f y| * (1 + ↑m) ^ k
          ≤ sem * (1 + ↑(Fintype.card (FinLatticeSites d N))) ^ k :=
            mul_le_mul hcoeff hpow (by positivity) hsem_nn
        _ = (1 + ↑(Fintype.card (FinLatticeSites d N))) ^ k * sem := by ring
    · simp only [h, dite_false, ContinuousLinearMap.zero_apply, abs_zero, zero_mul]
      positivity⟩

end GaussianField
