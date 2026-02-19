/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# NuclearSpace Instance for Schwartz Space

Derives the `NuclearSpace (SchwartzMap D ℝ)` instance from the topological
isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq` constructed in
`SchwartzNuclear.HermiteTensorProduct`.

## Main result

- `schwartz_nuclearSpace`: the `NuclearSpace` instance for Schwartz space
  on any nontrivial finite-dimensional real normed space.
-/

import SchwartzNuclear.HermiteTensorProduct

noncomputable section

open GaussianField

namespace GaussianField

/-! ## Deriving NuclearSpace from the Isomorphism

Given `equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`, we construct
the `NuclearSpace` instance by:
- **basis** m := equiv.symm (basisVec m)
- **coeff** m := coeffCLM m ∘ equiv
- **expansion**: from `rapidDecay_expansion` transferred through equiv
- **basis_growth**: from continuity of equiv.symm + seminorms of basisVec
- **coeff_decay**: from continuity of equiv + rapid decay of equiv(f) -/

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
private theorem schwartz_expansion_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq)
    (φ : SchwartzMap D ℝ →L[ℝ] ℝ) (f : SchwartzMap D ℝ) :
    φ f = ∑' m, (RapidDecaySeq.coeffCLM m (equiv f)) *
      φ (equiv.symm (RapidDecaySeq.basisVec m)) := by
  have h := RapidDecaySeq.rapidDecay_expansion
    (φ.comp equiv.symm.toContinuousLinearMap) (equiv f)
  simp only [ContinuousLinearMap.comp_apply] at h
  -- h : φ (↑equiv.symm (equiv f)) = ∑' m, (equiv f).val m * φ (↑equiv.symm (basisVec m))
  -- Need: φ f = ∑' m, coeffCLM m (equiv f) * φ (equiv.symm (basisVec m))
  -- LHS match: ↑equiv.symm (equiv f) = f
  have h_lhs : (equiv.symm : RapidDecaySeq →L[ℝ] SchwartzMap D ℝ) (equiv f) = f :=
    equiv.symm_apply_apply f
  rw [h_lhs] at h
  exact h

/-- Monotonicity of rapid-decay seminorms: for j ≤ j', seminorm j ≤ seminorm j'. -/
private theorem rapidDecaySeminorm_mono {j j' : ℕ} (hjj : j ≤ j') :
    RapidDecaySeq.rapidDecaySeminorm j ≤ RapidDecaySeq.rapidDecaySeminorm j' := by
  intro a
  show ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j ≤ ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j'
  apply (a.rapid_decay j).tsum_le_tsum _ (a.rapid_decay j')
  intro m
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg m)) hjj

/-- The sup of rapid-decay seminorms over a finset is bounded by the seminorm
at the max index. -/
private theorem finset_sup_rapidDecaySeminorm_le (s : Finset ℕ) :
    s.sup RapidDecaySeq.rapidDecaySeminorm ≤
      RapidDecaySeq.rapidDecaySeminorm (s.sup id) := by
  apply Finset.sup_le
  intro j hj
  exact rapidDecaySeminorm_mono (Finset.le_sup (f := id) hj)

/-- The sup of rapid-decay seminorms evaluated at a basis vector gives
polynomial growth. -/
private theorem finset_sup_rapidDecaySeminorm_basisVec_le (s : Finset ℕ) (m : ℕ) :
    (s.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) ≤
      (1 + (m : ℝ)) ^ (s.sup id) := by
  calc (s.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m)
      ≤ RapidDecaySeq.rapidDecaySeminorm (s.sup id) (RapidDecaySeq.basisVec m) :=
        finset_sup_rapidDecaySeminorm_le s (RapidDecaySeq.basisVec m)
    _ = (1 + (m : ℝ)) ^ (s.sup id) :=
        RapidDecaySeq.rapidDecaySeminorm_basisVec _ m

omit [FiniteDimensional ℝ D] in
private theorem schwartz_basis_growth_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq) :
    ∀ (i : ℕ × ℕ), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, SchwartzMap.seminorm ℝ i.1 i.2
      (equiv.symm (RapidDecaySeq.basisVec m)) ≤ C * (1 + (m : ℝ)) ^ s := by
  intro ⟨k, l⟩
  -- The composition (seminorm k l) ∘ equiv.symm is a continuous seminorm on RapidDecaySeq
  set q : Seminorm ℝ RapidDecaySeq :=
    (SchwartzMap.seminorm ℝ k l).comp equiv.symm.toLinearMap with hq_def
  have hq_cont : Continuous q :=
    ((schwartz_withSeminorms ℝ D ℝ).continuous_seminorm ⟨k, l⟩).comp
      equiv.symm.continuous
  -- By Seminorm.bound_of_continuous, q is bounded by finitely many rapid-decay seminorms
  obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
    Seminorm.bound_of_continuous RapidDecaySeq.rapidDecay_withSeminorms q hq_cont
  -- Extract: for all a, seminorm k l (equiv.symm a) ≤ C_nn * (s_fin.sup rapidDecaySeminorm) a
  set N := s_fin.sup id
  have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
  refine ⟨(C_nn : ℝ), hC_pos, N, fun m => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (equiv.symm (RapidDecaySeq.basisVec m))
      = q (RapidDecaySeq.basisVec m) := rfl
    _ ≤ C_nn • (s_fin.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) :=
        hle (RapidDecaySeq.basisVec m)
    _ ≤ (C_nn : ℝ) * (1 + (m : ℝ)) ^ N := by
        simp only [NNReal.smul_def, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (finset_sup_rapidDecaySeminorm_basisVec_le s_fin m)
          (NNReal.coe_nonneg C_nn)

omit [FiniteDimensional ℝ D] in
private theorem schwartz_coeff_decay_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq) :
    ∀ (k : ℕ), ∃ C > 0, ∃ (s : Finset (ℕ × ℕ)),
    ∀ (f : SchwartzMap D ℝ) (m : ℕ),
      |RapidDecaySeq.coeffCLM m (equiv f)| * (1 + (m : ℝ)) ^ k ≤
        C * (s.sup (fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l)) f := by
  intro k
  -- |coeffCLM m (equiv f)| = |(equiv f).val m|
  -- |(equiv f).val m| * (1+m)^k ≤ ∑' n, |(equiv f).val n| * (1+n)^k
  --   = rapidDecaySeminorm k (equiv f)
  -- From continuity of equiv: rapidDecaySeminorm k (equiv f) ≤ C * (sup Schwartz seminorms) f
  -- Get continuity bound for equiv
  set q : Seminorm ℝ (SchwartzMap D ℝ) :=
    (RapidDecaySeq.rapidDecaySeminorm k).comp equiv.toLinearMap with hq_def
  have hq_cont : Continuous q :=
    (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm k).comp
      equiv.continuous
  obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ D ℝ) q hq_cont
  have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
  refine ⟨(C_nn : ℝ), hC_pos, s_fin, fun f m => ?_⟩
  -- |coeffCLM m (equiv f)| * (1+m)^k ≤ rapidDecaySeminorm k (equiv f)
  have h_le_tsum : |RapidDecaySeq.coeffCLM m (equiv f)| * (1 + (m : ℝ)) ^ k ≤
      RapidDecaySeq.rapidDecaySeminorm k (equiv f) := by
    show |(equiv f).val m| * (1 + (m : ℝ)) ^ k ≤
      ∑' n, |(equiv f).val n| * (1 + (n : ℝ)) ^ k
    exact ((equiv f).rapid_decay k).le_tsum m
      (fun j _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg j k))
  -- rapidDecaySeminorm k (equiv f) ≤ C_nn * (s_fin.sup Schwartz seminorms) f
  have h_bound : RapidDecaySeq.rapidDecaySeminorm k (equiv f) ≤
      (C_nn : ℝ) * (s_fin.sup (fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l)) f := by
    have := hle f
    simp only [hq_def, Seminorm.comp_apply, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul] at this
    exact this
  linarith

/-! ## The NuclearSpace Instance -/

/-- **Schwartz space is a nuclear Fréchet space.**

The instance uses the Schwartz seminorm family `(k, l) ↦ p_{k,l}` and a
basis/coefficient system derived from the topological isomorphism
`SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

Proved via the topological isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`
constructed from multi-dimensional Hermite analysis. -/
noncomputable instance schwartz_nuclearSpace [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D ℝ
  basis m := (schwartzRapidDecayEquiv D).symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp
    (schwartzRapidDecayEquiv D).toContinuousLinearMap
  expansion := schwartz_expansion_from_equiv (schwartzRapidDecayEquiv D)
  basis_growth := schwartz_basis_growth_from_equiv (schwartzRapidDecayEquiv D)
  coeff_decay := schwartz_coeff_decay_from_equiv (schwartzRapidDecayEquiv D)

end GaussianField
