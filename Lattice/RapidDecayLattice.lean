/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rapidly Decaying Functions on ℤ^d

Defines `RapidDecayLattice d`, the space of rapidly decaying functions on ℤ^d,
and establishes its DyninMityaginSpace structure via a continuous linear
equivalence with `RapidDecaySeq`.

## Main definitions

- `RapidDecayLattice d` — rapidly decaying functions on ℤ^d
- `latticeRapidDecaySeminorm d k` — seminorm: `∑_x |f(x)| (1+|x|)^k`
- `latticeEnum d` — shell enumeration `ℤ^d ≃ ℕ`
- `latticeRapidDecayEquiv d` — CLE to `RapidDecaySeq`
- `DyninMityaginSpace` instance via `ofRapidDecayEquiv`
- `HasPointEval` instance

## Key difficulty

The CLE proof needs to show that the shell enumeration preserves rapid decay:
`latticeNorm (latticeEnum.symm m) ≤ C · m^{1/d}`. This follows because the
number of points in ℤ^d with ℓ¹ norm ≤ R grows as ~R^d, so the m-th point
has norm ~m^{1/d}.

## References

- Dynin-Mityagin, via the general transfer constructor `ofRapidDecayEquiv`
-/

import Lattice.Sites
import Nuclear.NuclearTensorProduct
import Nuclear.PointEval
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

namespace GaussianField

/-! ## Rapidly Decaying Lattice Functions -/

/-- A rapidly decaying function on ℤ^d: `val : (Fin d → ℤ) → ℝ` such that
`∑_x |val x| · (1 + latticeNorm x)^k` converges for all `k : ℕ`. -/
structure RapidDecayLattice (d : ℕ) where
  val : (Fin d → ℤ) → ℝ
  rapid_decay : ∀ k : ℕ, Summable (fun x => |val x| * (1 + latticeNorm x) ^ k)

namespace RapidDecayLattice

variable {d : ℕ}

@[ext]
theorem ext {a b : RapidDecayLattice d} (h : ∀ x, a.val x = b.val x) : a = b := by
  cases a; cases b; congr 1; exact funext h

/-! ### Weight function lemmas -/

theorem weight_pos (x : Fin d → ℤ) (k : ℕ) : (0 : ℝ) < (1 + latticeNorm x) ^ k := by
  apply pow_pos
  linarith [latticeNorm_nonneg x]

theorem weight_nonneg (x : Fin d → ℤ) (k : ℕ) : (0 : ℝ) ≤ (1 + latticeNorm x) ^ k :=
  le_of_lt (weight_pos x k)

/-! ### Algebraic structure -/

instance instZero : Zero (RapidDecayLattice d) where
  zero := ⟨0, fun k => by simp [summable_zero]⟩

@[simp] theorem zero_val (x : Fin d → ℤ) : (0 : RapidDecayLattice d).val x = 0 := rfl

instance instAdd : Add (RapidDecayLattice d) where
  add a b := ⟨a.val + b.val, fun k => by
    apply Summable.of_nonneg_of_le
    · intro x; exact mul_nonneg (abs_nonneg _) (weight_nonneg x k)
    · intro x; simp only [Pi.add_apply]
      calc |a.val x + b.val x| * (1 + latticeNorm x) ^ k
          ≤ (|a.val x| + |b.val x|) * (1 + latticeNorm x) ^ k :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg x k)
        _ = |a.val x| * (1 + latticeNorm x) ^ k +
            |b.val x| * (1 + latticeNorm x) ^ k := add_mul _ _ _
    · exact (a.rapid_decay k).add (b.rapid_decay k)⟩

@[simp] theorem add_val (a b : RapidDecayLattice d) (x : Fin d → ℤ) :
    (a + b).val x = a.val x + b.val x := rfl

instance instNeg : Neg (RapidDecayLattice d) where
  neg a := ⟨fun x => -a.val x, fun k => by
    simp only [abs_neg]; exact a.rapid_decay k⟩

@[simp] theorem neg_val (a : RapidDecayLattice d) (x : Fin d → ℤ) :
    (-a).val x = -a.val x := rfl

instance instSMul : SMul ℝ (RapidDecayLattice d) where
  smul r a := ⟨fun x => r * a.val x, fun k => by
    have h : (fun x => |r * a.val x| * (1 + latticeNorm x) ^ k) =
             fun x => |r| * (|a.val x| * (1 + latticeNorm x) ^ k) := by
      ext x; rw [abs_mul, mul_assoc]
    rw [h]
    exact (a.rapid_decay k).const_smul |r|⟩

@[simp] theorem smul_val (r : ℝ) (a : RapidDecayLattice d) (x : Fin d → ℤ) :
    (r • a).val x = r * a.val x := rfl

instance instAddCommGroup : AddCommGroup (RapidDecayLattice d) where
  add_assoc a b c := ext fun x => add_assoc _ _ _
  zero_add a := ext fun x => zero_add _
  add_zero a := ext fun x => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun x => neg_add_cancel _
  add_comm a b := ext fun x => add_comm _ _

instance instModule : Module ℝ (RapidDecayLattice d) where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-! ### Seminorm family -/

/-- The k-th seminorm on rapidly decaying lattice functions:
`∑_x |f(x)| · (1 + latticeNorm x)^k`. -/
def latticeRapidDecaySeminorm (d : ℕ) (k : ℕ) :
    Seminorm ℝ (RapidDecayLattice d) where
  toFun a := ∑' x, |a.val x| * (1 + latticeNorm x) ^ k
  map_zero' := by simp [zero_val, tsum_zero]
  add_le' a b := by
    calc ∑' x, |(a + b).val x| * (1 + latticeNorm x) ^ k
        ≤ ∑' x, (|a.val x| * (1 + latticeNorm x) ^ k +
                  |b.val x| * (1 + latticeNorm x) ^ k) := by
          exact ((a + b).rapid_decay k).tsum_le_tsum
            (fun x => by simp only [add_val]
                         calc |a.val x + b.val x| * (1 + latticeNorm x) ^ k
                             ≤ (|a.val x| + |b.val x|) * (1 + latticeNorm x) ^ k :=
                               mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg x k)
                           _ = _ := add_mul _ _ _)
            ((a.rapid_decay k).add (b.rapid_decay k))
      _ = ∑' x, |a.val x| * (1 + latticeNorm x) ^ k +
          ∑' x, |b.val x| * (1 + latticeNorm x) ^ k :=
          (a.rapid_decay k).tsum_add (b.rapid_decay k)
  neg' a := by
    congr 1; ext x; rw [neg_val, abs_neg]
  smul' r a := by
    show ∑' x, |r * a.val x| * (1 + latticeNorm x) ^ k =
      ‖r‖ * ∑' x, |a.val x| * (1 + latticeNorm x) ^ k
    simp_rw [abs_mul, Real.norm_eq_abs, mul_assoc]
    exact tsum_mul_left

/-! ### Topology from seminorms -/

instance instTopologicalSpace : TopologicalSpace (RapidDecayLattice d) :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) (latticeRapidDecaySeminorm d)).topology

theorem lattice_withSeminorms :
    WithSeminorms (latticeRapidDecaySeminorm d :
      ℕ → Seminorm ℝ (RapidDecayLattice d)) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (RapidDecayLattice d) :=
  lattice_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ (RapidDecayLattice d) :=
  lattice_withSeminorms.continuousSMul

/-! ### Enumeration of ℤ^d

We need an explicit bijection `(Fin d → ℤ) ≃ ℕ` with polynomial norm growth.
A shell enumeration (ordered by ℓ¹ norm, ties broken lexicographically) works.

Key property: `latticeNorm (enum.symm m) ≤ C · m^{1/d}` because the number
of ℤ^d points with ℓ¹ norm ≤ R is O(R^d).

For now this is axiomatized; the explicit construction is nontrivial but
standard (Cantor-style diagonal enumeration for d=1, iterated pairing for d>1). -/

/-- Shell enumeration of ℤ^d: bijection with ℕ ordered approximately by ℓ¹ norm. -/
axiom latticeEnum (d : ℕ) : (Fin d → ℤ) ≃ ℕ

/-- The enumeration has polynomial norm growth: the m-th point has
ℓ¹ norm bounded by C · (1+m)^{1/d}. This is the key bound for the CLE proof. -/
axiom latticeEnum_norm_bound (d : ℕ) :
    ∃ C > (0 : ℝ), ∀ m : ℕ,
    latticeNorm ((latticeEnum d).symm m) ≤ C * (1 + (m : ℝ)) ^ ((1 : ℝ) / d)

/-- Converse bound: points with small norm have small index. -/
axiom latticeEnum_index_bound (d : ℕ) :
    ∃ C > (0 : ℝ), ∀ x : Fin d → ℤ,
    (latticeEnum d x : ℝ) ≤ C * (1 + latticeNorm x) ^ (d : ℝ)

/-! ### Basis and coefficients -/

/-- Delta function at a lattice site. -/
def latticeBasisAt (x : Fin d → ℤ) : RapidDecayLattice d where
  val y := if y = x then 1 else 0
  rapid_decay k := by
    apply summable_of_ne_finset_zero (s := {x})
    intro y hy
    simp only [Finset.mem_singleton] at hy
    simp [hy]

/-- The m-th basis vector: delta function at the m-th site in the enumeration. -/
def latticeBasisVec (d : ℕ) (m : ℕ) : RapidDecayLattice d :=
  latticeBasisAt ((latticeEnum d).symm m)

/-- The m-th coefficient CLM: evaluation at the m-th site. -/
def latticeCoeffCLM (d : ℕ) (m : ℕ) : RapidDecayLattice d →L[ℝ] ℝ where
  toLinearMap :=
    { toFun := fun a => a.val ((latticeEnum d).symm m)
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by simp [smul_eq_mul] }
  cont := by
    set f : RapidDecayLattice d →ₗ[ℝ] ℝ :=
      { toFun := fun a => a.val ((latticeEnum d).symm m)
        map_add' := fun _ _ => rfl
        map_smul' := fun r a => by simp [smul_eq_mul] }
    show Continuous f
    apply Seminorm.cont_withSeminorms_normedSpace ℝ lattice_withSeminorms
    refine ⟨{0}, 1, ?_⟩
    rw [Seminorm.le_def]
    intro a
    simp only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul]
    show ‖f a‖ ≤ latticeRapidDecaySeminorm d 0 a
    rw [Real.norm_eq_abs]
    show |a.val ((latticeEnum d).symm m)| ≤
      ∑' x, |a.val x| * (1 + latticeNorm x) ^ 0
    calc |a.val ((latticeEnum d).symm m)|
        = |a.val ((latticeEnum d).symm m)| * (1 + latticeNorm ((latticeEnum d).symm m)) ^ 0 := by
          simp [pow_zero]
      _ ≤ ∑' x, |a.val x| * (1 + latticeNorm x) ^ 0 :=
          (a.rapid_decay 0).le_tsum ((latticeEnum d).symm m)
            (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))

/-! ### CLE to RapidDecaySeq -/

/-- Continuous linear equivalence between `RapidDecayLattice d` and `RapidDecaySeq`,
obtained by reindexing via the shell enumeration `latticeEnum d`.

The key proof obligation is that reindexing preserves rapid decay:
- Forward: `|f(enum.symm m)| * (1+m)^k ≤ C_k * Σ_x |f(x)| * (1+|x|)^{k·d}`
  follows from `latticeEnum_norm_bound`.
- Backward: similar using `latticeEnum_index_bound`. -/
axiom latticeRapidDecayEquiv (d : ℕ) :
    RapidDecayLattice d ≃L[ℝ] RapidDecaySeq

/-! ### DyninMityaginSpace instance -/

/-- `RapidDecayLattice d` is a DyninMityaginSpace, established via the CLE
to `RapidDecaySeq` and the general transfer constructor `ofRapidDecayEquiv`. -/
noncomputable instance lattice_dyninMityaginSpace :
    DyninMityaginSpace (RapidDecayLattice d) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (latticeRapidDecaySeminorm d)
    lattice_withSeminorms
    (latticeRapidDecayEquiv d)

end RapidDecayLattice

/-! ### HasPointEval instance -/

/-- Rapidly decaying lattice functions can be evaluated at ℤ^d points. -/
instance rapidDecayLattice_hasPointEval (d : ℕ) :
    HasPointEval (RapidDecayLattice d) (Fin d → ℤ) where
  pointEval f x := f.val x

end GaussianField
