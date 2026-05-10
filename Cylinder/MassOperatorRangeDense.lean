/- 
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Range density of the cylinder mass operator

Proves that the cylinder mass operator has dense range in `ell2'` by
constructing explicit preimages of the standard basis vectors.
-/

import Cylinder.MassOperatorConstruction
import HeatKernel.GreenInvariance
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

private def cylinderMassOperator_witness
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    CylinderTestFunction L :=
  NuclearTensorProduct.pure
    (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1)
    ((resolventMultiplierCLE
      (resolventFreq_pos L mass hmass (Nat.unpair n).1)).symm
      (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2))

private theorem cylinderMassOperator_witness_eq_basis
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    cylinderMassOperator L mass hmass
      (cylinderMassOperator_witness L mass hmass n) =
    lp.single 2 n (1 : ℝ) := by
  ext m
  set a0 := (Nat.unpair n).1
  set b0 := (Nat.unpair n).2
  set a := (Nat.unpair m).1
  set b := (Nat.unpair m).2
  set hω0 : 0 < resolventFreq L mass a0 := resolventFreq_pos L mass hmass a0
  set h0 : SchwartzMap ℝ ℝ :=
    (resolventMultiplierCLE hω0).symm
      (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b0)
  have hm_pair : Nat.pair a b = m := by
    simp [a, b]
  have hn_pair : Nat.pair a0 b0 = n := by
    simp [a0, b0]
  have hslice :
      ntpSliceSchwartz L a (cylinderMassOperator_witness L mass hmass n) =
        (if a = a0 then 1 else 0 : ℝ) • h0 := by
    simp [cylinderMassOperator_witness, a0, b0, a, h0, ntpSliceSchwartz_pure,
      smoothCircle_coeff_basis]
  rw [cylinderMassOperator_formula, hslice]
  by_cases ha : a = a0
  · have hres :
        resolventMultiplierCLM hω0 h0 =
          DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b0 := by
      dsimp [h0]
      exact (resolventMultiplierCLE hω0).apply_symm_apply _
    simp [ha, a, a0, b0, hres,
      DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]
    rw [← hm_pair, ← hn_pair]
    simp [Pi.single_apply, ha]
  · simp [ha, a, a0]
    rw [← hm_pair, ← hn_pair]
    simp [ha]

private theorem ell2_single_span_dense :
    (Submodule.span ℝ (Set.range (fun n : ℕ => (lp.single 2 n (1 : ℝ) : ell2')))).topologicalClosure = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h_sum : HasSum (fun m => lp.single 2 m ((x : ℕ → ℝ) m)) x :=
    lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
  exact mem_closure_of_tendsto h_sum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun s =>
      Submodule.sum_mem _ fun m _ => by
        have hs :
            lp.single 2 m ((x : ℕ → ℝ) m) =
              (x : ℕ → ℝ) m • (lp.single 2 m (1 : ℝ) : ell2') := by
          rw [← lp.single_smul]
          simp
        rw [hs]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))

/-- The cylinder mass operator has dense range in `ell2'`. -/
theorem cylinderMassOperator_range_dense (mass : ℝ) (hmass : 0 < mass) :
    DenseRange (⇑(cylinderMassOperator L mass hmass) : CylinderTestFunction L → ell2') := by
  rw [denseRange_iff_closure_range]
  let T := cylinderMassOperator L mass hmass
  change closure (↑T.range : Set ell2') = Set.univ
  have hspan :
      Submodule.span ℝ (Set.range (fun n : ℕ => (lp.single 2 n (1 : ℝ) : ell2'))) ≤ T.range := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨cylinderMassOperator_witness L mass hmass n,
      cylinderMassOperator_witness_eq_basis L mass hmass n⟩
  have hrange_top : T.range.topologicalClosure = ⊤ := by
    apply le_antisymm le_top
    rw [← ell2_single_span_dense]
    exact Submodule.topologicalClosure_mono hspan
  rw [← Submodule.topologicalClosure_coe, hrange_top]
  rfl

end GaussianField

end
