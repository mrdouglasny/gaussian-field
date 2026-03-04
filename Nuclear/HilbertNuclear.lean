/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bridge: DyninMityaginSpace → IsHilbertNuclear

Connects gaussian-field's `NuclearSpace` (Pietsch characterization) to bochner's
`IsHilbertNuclear` (Hilbertian seminorms with Hilbert-Schmidt embeddings), and
proves `IsHilbertNuclear RapidDecaySeq`.

## Strategy

1. Bridge `GaussianField.NuclearSpace E` to `IsNuclear E` (bochner): the definitions
   differ only in using `‖·‖` vs `|·|` for ℝ-valued maps, which are equal.
2. Apply bochner's `isHilbertNuclear_of_nuclear` to get `IsHilbertNuclear`.
3. Provide a CLE transfer lemma for `IsHilbertNuclear`.

## References

- Pietsch, "Nuclear Locally Convex Spaces" (1972), §4
- Trèves, "Topological Vector Spaces", Ch. 50-51
-/

import Nuclear.NuclearSpace
import Nuclear.NuclearTensorProduct
import Minlos.PietschBridge

noncomputable section

namespace GaussianField

open RapidDecaySeq

/-! ### Bridge: NuclearSpace → IsNuclear -/

/-- Bridge from gaussian-field's `NuclearSpace` to bochner's `IsNuclear`.

The two definitions are mathematically identical: both assert Pietsch nuclear
dominance. The only syntactic difference is `‖f n x‖` vs `|f n x|` in the
functional bound, which are equal for `ℝ`-valued maps by `Real.norm_eq_abs`. -/
theorem nuclearSpace_isNuclear (E : Type*)
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [h : NuclearSpace E] : IsNuclear E := by
  intro p hp
  obtain ⟨q, hq_cont, hpq, f, c, hc_nn, hc_sum, hf_bound, hp_nuc⟩ :=
    h.nuclear_dominance p hp
  exact ⟨q, hq_cont, hpq, f, c, hc_nn, hc_sum,
    fun n x => by rw [← Real.norm_eq_abs]; exact hf_bound n x,
    hp_nuc⟩

/-! ### IsHilbertNuclear RapidDecaySeq -/

/-- **Rapid decay sequences form a Hilbert-nuclear space.**

The chain: `DyninMityaginSpace RapidDecaySeq` (instance in NuclearTensorProduct)
→ `NuclearSpace RapidDecaySeq` (via `toNuclearSpace`)
→ `IsNuclear RapidDecaySeq` (bridge above)
→ `IsHilbertNuclear RapidDecaySeq` (via bochner's `isHilbertNuclear_of_nuclear`). -/
instance rapidDecaySeq_isHilbertNuclear : IsHilbertNuclear RapidDecaySeq := by
  haveI : NuclearSpace RapidDecaySeq := DyninMityaginSpace.toNuclearSpace RapidDecaySeq
  exact isHilbertNuclear_of_nuclear
    (nuclearSpace_isNuclear RapidDecaySeq)
    rapidDecaySeminorm
    rapidDecay_withSeminorms
    (fun n => rapidDecay_withSeminorms.continuous_seminorm n)

/-! ### CLE Transfer for IsHilbertNuclear -/

/-- Transfer `IsHilbertNuclear` along a continuous linear equivalence.

If `F` is Hilbert-nuclear and `e : E ≃L[ℝ] F`, then `E` is Hilbert-nuclear:
pull back the Hilbertian seminorms via `(p n).comp e.toLinearMap`, using
mathlib's `Topology.IsInducing.withSeminorms` to transfer the topology. -/
theorem IsHilbertNuclear.of_equiv
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    (e : E ≃L[ℝ] F) [IsHilbertNuclear F] : IsHilbertNuclear E where
  nuclear_hilbert_embeddings := by
    obtain ⟨p, hp_hilb, hp_with, hp_hs⟩ := IsHilbertNuclear.nuclear_hilbert_embeddings (E := F)
    -- Pull back seminorms: q n x = p n (e x)
    set q : ℕ → Seminorm ℝ E := fun n => (p n).comp e.toLinearMap with hq_def
    refine ⟨q, ?_, ?_, ?_⟩
    · -- Each pulled-back seminorm is Hilbertian
      intro n x y
      simp only [hq_def, Seminorm.comp_apply, map_add, map_sub]
      exact hp_hilb n (e x) (e y)
    · -- WithSeminorms: use mathlib's IsInducing.withSeminorms
      have : q = SeminormFamily.comp p e.toLinearMap := by ext; rfl
      rw [this]
      exact e.toHomeomorph.isInducing.withSeminorms hp_with
    · -- Consecutive HS embeddings are preserved
      intro n
      obtain ⟨hle, C, hC⟩ := hp_hs n
      refine ⟨fun x => ?_, C, fun N v hv => ?_⟩
      · simp only [hq_def, Seminorm.comp_apply]
        exact hle (e x)
      · -- e ∘ v is p(n+1)-orthonormal, so the HS bound transfers
        have hev : (p (n + 1)).IsOrthonormalSeq (fun i => e (v i)) := by
          intro i j
          show (p (n + 1)).innerProd (e (v i)) (e (v j)) = _
          simp only [Seminorm.innerProd, ← map_add, ← map_sub]
          exact hv i j
        exact hC N (fun i => e (v i)) hev

end GaussianField
