/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generalized Tensor Product Functor

Extends `nuclearTensorProduct_mapCLM` from endomorphisms to general CLMs
between different DyninMityagin spaces.

## Main definitions

- `nuclearTensorProduct_mapCLM_general` — `(T₁ ⊗ T₂)` for
  `T₁ : E₁ →L[ℝ] F₁` and `T₂ : E₂ →L[ℝ] F₂`, giving
  `NTP(E₁, E₂) →L[ℝ] NTP(F₁, F₂)`

## Mathematical background

The construction is the same as `nuclearTensorProduct_mapCLM`:
on the DM basis, `(T₁ ⊗ T₂)(basisVec m) = pure(T₁ ψ_a, T₂ ψ_b)`
where `m = pair(a, b)`. The coefficients of this pure tensor in the
output DM basis give a rapid-decay sequence, and the extension by
linearity/continuity gives the CLM.

The difference from `nuclearTensorProduct_mapCLM` is purely at the type
level: the input and output NTP spaces can be different.

## References

- Treves, *Topological Vector Spaces*, Ch. 50 (nuclear spaces)
-/

import Nuclear.NuclearTensorProduct
import Nuclear.TensorProductFunctorAxioms

noncomputable section

namespace GaussianField

open NuclearTensorProduct

/-! ## Generalized tensor product of CLMs

The key construction: `mapCLM_general T₁ T₂` acts on `f : NTP E₁ E₂ = RapidDecaySeq` by
mapping each basis vector `basisVec m ↦ pure(T₁(ψ_a), T₂(ψ_b))` where `(a,b) = unpair(m)`,
with `pure` creating an element of `NTP F₁ F₂`.

At the coefficient level:
`(mapCLM_general T₁ T₂ f).val n = ∑' m, f.val m · coeff_{F₁} a'(T₁(ψ_{E₁} a)) · coeff_{F₂} b'(T₂(ψ_{E₂} b))`
where `(a,b) = unpair(m)`, `(a',b') = unpair(n)`, and `coeff_{F_i}` / `ψ_{E_i}` refer to the
DyninMityagin coefficients/basis of the respective spaces. -/

section GeneralMapCLM

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    {F₁ : Type*} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
    [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [DyninMityaginSpace F₁]
    {F₂ : Type*} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
    [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [DyninMityaginSpace F₂]

/-- The image of basis vector `m` under `T₁ ⊗ T₂` (general version):
`Φ(m) = pure(T₁(ψ^{E₁}_a), T₂(ψ^{E₂}_b))` where `(a,b) = unpair(m)`,
with the result living in `NTP F₁ F₂`. -/
private def mapImageGen (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) (m : ℕ) :
    NuclearTensorProduct F₁ F₂ :=
  NuclearTensorProduct.pure
    (T₁ (DyninMityaginSpace.basis (Nat.unpair m).1))
    (T₂ (DyninMityaginSpace.basis (Nat.unpair m).2))

/-- Polynomial bound on seminorms of `mapImageGen`.
`seminorm_k(Φ(m)) ≤ K * (1+m)^S`.
Same proof as `mapImage_seminorm_bound` but with cross-type CLMs. -/
private theorem mapImageGen_seminorm_bound (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) (k : ℕ) :
    ∃ K > 0, ∃ S : ℕ, ∀ m,
    RapidDecaySeq.rapidDecaySeminorm k (mapImageGen T₁ T₂ m) ≤ K * (1 + (m : ℝ)) ^ S := by
  classical
  -- pure_seminorm_bound gives: seminorm_k(pure f₁ f₂) ≤ C * (s₁.sup p_{F₁}) f₁ * (s₂.sup p_{F₂}) f₂
  obtain ⟨C, s₁, s₂, hpure⟩ := pure_seminorm_bound (E₁ := F₁) (E₂ := F₂) k
  -- Bound (s₁.sup p_{F₁})(T₁(basis^{E₁} a)) via CLM continuity + basis_growth
  have hT₁_cont : Continuous ((s₁.sup DyninMityaginSpace.p).comp T₁.toLinearMap) := by
    apply Continuous.comp _ T₁.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₁)
    show Continuous fun (x : F₁) =>
      (Seminorm.coeFnAddMonoidHom ℝ F₁) (∑ i ∈ s₁, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  obtain ⟨t₁, C₁nn, hC₁nn, hle₁⟩ := Seminorm.bound_of_continuous
    DyninMityaginSpace.h_with _ hT₁_cont
  have hT₂_cont : Continuous ((s₂.sup DyninMityaginSpace.p).comp T₂.toLinearMap) := by
    apply Continuous.comp _ T₂.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₂)
    show Continuous fun (x : F₂) =>
      (Seminorm.coeFnAddMonoidHom ℝ F₂) (∑ i ∈ s₂, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  obtain ⟨t₂, C₂nn, hC₂nn, hle₂⟩ := Seminorm.bound_of_continuous
    DyninMityaginSpace.h_with _ hT₂_cont
  obtain ⟨D₁, hD₁, S₁, hbnd₁⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p t₁ DyninMityaginSpace.basis
    (fun i _ => DyninMityaginSpace.basis_growth i)
  obtain ⟨D₂, hD₂, S₂, hbnd₂⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p t₂ DyninMityaginSpace.basis
    (fun i _ => DyninMityaginSpace.basis_growth i)
  have hC₁_pos : (0:ℝ) < ↑C₁nn := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC₁nn)
  have hC₂_pos : (0:ℝ) < ↑C₂nn := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC₂nn)
  refine ⟨(↑C + 1) * (↑C₁nn * D₁) * (↑C₂nn * D₂), by positivity, S₁ + S₂, fun m => ?_⟩
  set a := (Nat.unpair m).1; set b := (Nat.unpair m).2
  have ha_le : (1 + (a : ℝ)) ≤ (1 + (m : ℝ)) :=
    add_le_add_right (Nat.cast_le.mpr (Nat.unpair_left_le m)) 1
  have hb_le : (1 + (b : ℝ)) ≤ (1 + (m : ℝ)) :=
    add_le_add_right (Nat.cast_le.mpr (Nat.unpair_right_le m)) 1
  have hT₁_bnd : (s₁.sup DyninMityaginSpace.p) (T₁ (DyninMityaginSpace.basis a)) ≤
      ↑C₁nn * D₁ * (1 + (m : ℝ)) ^ S₁ := by
    calc (s₁.sup DyninMityaginSpace.p) (T₁ (DyninMityaginSpace.basis a))
        ≤ ↑C₁nn * (t₁.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis a) := by
          have := hle₁ (DyninMityaginSpace.basis a)
          simp only [Seminorm.comp_apply] at this; exact this
      _ ≤ ↑C₁nn * (D₁ * (1 + (a : ℝ)) ^ S₁) :=
          mul_le_mul_of_nonneg_left (hbnd₁ a) (NNReal.coe_nonneg _)
      _ ≤ ↑C₁nn * D₁ * (1 + (m : ℝ)) ^ S₁ := by
          rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) ha_le S₁) (le_of_lt hD₁)
  have hT₂_bnd : (s₂.sup DyninMityaginSpace.p) (T₂ (DyninMityaginSpace.basis b)) ≤
      ↑C₂nn * D₂ * (1 + (m : ℝ)) ^ S₂ := by
    calc (s₂.sup DyninMityaginSpace.p) (T₂ (DyninMityaginSpace.basis b))
        ≤ ↑C₂nn * (t₂.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis b) := by
          have := hle₂ (DyninMityaginSpace.basis b)
          simp only [Seminorm.comp_apply] at this; exact this
      _ ≤ ↑C₂nn * (D₂ * (1 + (b : ℝ)) ^ S₂) :=
          mul_le_mul_of_nonneg_left (hbnd₂ b) (NNReal.coe_nonneg _)
      _ ≤ ↑C₂nn * D₂ * (1 + (m : ℝ)) ^ S₂ := by
          rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hb_le S₂) (le_of_lt hD₂)
  calc RapidDecaySeq.rapidDecaySeminorm k (mapImageGen T₁ T₂ m)
      ≤ ↑C * (s₁.sup DyninMityaginSpace.p) (T₁ (DyninMityaginSpace.basis a)) *
        (s₂.sup DyninMityaginSpace.p) (T₂ (DyninMityaginSpace.basis b)) := hpure _ _
    _ ≤ ↑C * (↑C₁nn * D₁ * (1 + (m : ℝ)) ^ S₁) * (↑C₂nn * D₂ * (1 + (m : ℝ)) ^ S₂) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hT₁_bnd (NNReal.coe_nonneg _))
          hT₂_bnd (apply_nonneg _ _)
          (mul_nonneg (NNReal.coe_nonneg _) (by positivity))
    _ = ↑C * (↑C₁nn * D₁) * (↑C₂nn * D₂) * (1 + (m : ℝ)) ^ (S₁ + S₂) := by
        rw [pow_add]; ring
    _ ≤ (↑C + 1) * (↑C₁nn * D₁) * (↑C₂nn * D₂) * (1 + (m : ℝ)) ^ (S₁ + S₂) := by
        gcongr; linarith [NNReal.coe_nonneg C]

set_option maxHeartbeats 400000 in
private theorem mapInnerGen_summable (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (f : RapidDecaySeq) (n : ℕ) :
    Summable (fun m => f.val m * (mapImageGen T₁ T₂ m).val n) := by
  classical
  obtain ⟨K, hK, S, hbnd⟩ := mapImageGen_seminorm_bound T₁ T₂ 0
  refine Summable.of_norm_bounded ((f.rapid_decay S).mul_left K) (fun m => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(mapImageGen T₁ T₂ m).val n| ≤ K * (1 + (m : ℝ)) ^ S := by
    have := val_le_seminorm (mapImageGen T₁ T₂ m) n 0
    simp only [pow_zero, mul_one] at this
    exact le_trans this (hbnd m)
  calc |f.val m| * |(mapImageGen T₁ T₂ m).val n|
      ≤ |f.val m| * (K * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = K * (|f.val m| * (1 + (m : ℝ)) ^ S) := by ring

/-- Summability of `∑ₘ |fₘ| * seminorm_k(Φ(m))` using polynomial bound on Φ. -/
private theorem mapCoeffGen_seminorm_summable (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (f : RapidDecaySeq) (k : ℕ) :
    Summable (fun m => |f.val m| *
      RapidDecaySeq.rapidDecaySeminorm k (mapImageGen T₁ T₂ m)) := by
  classical
  obtain ⟨K, hK, S, hbnd⟩ := mapImageGen_seminorm_bound T₁ T₂ k
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun m => mul_le_mul_of_nonneg_left (hbnd m) (abs_nonneg _))
    (((f.rapid_decay S).mul_left K).congr (fun m => by ring))

/-- Pointwise bound on the mapped value times weight:
`|Φ(m).val n| * (1+n)^k ≤ seminorm_{k+2}(Φ(m)) / (1+n)^2`. -/
private theorem mapImageGen_val_weight_bound (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (m n k : ℕ) :
    |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
    RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) *
      ((1 + (n : ℝ)) ^ 2)⁻¹ := by
  have hn_pos : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  rw [le_mul_inv_iff₀ (pow_pos hn_pos 2)]
  calc |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k * (1 + (n : ℝ)) ^ 2
      = |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ (k + 2) := by rw [pow_add]; ring
    _ ≤ RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) :=
        val_le_seminorm _ n (k + 2)

/-- Summability of the absolute-value series for mapCLM_general. -/
private theorem mapInnerGen_abs_summable (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (f : RapidDecaySeq) (n : ℕ) :
    Summable (fun m => |f.val m| * |(mapImageGen T₁ T₂ m).val n|) := by
  classical
  obtain ⟨K, _, S, hbnd⟩ := mapImageGen_seminorm_bound T₁ T₂ 0
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((f.rapid_decay S).mul_left K)
  have h1 : |(mapImageGen T₁ T₂ m).val n| ≤ K * (1 + (m : ℝ)) ^ S := by
    have := val_le_seminorm (mapImageGen T₁ T₂ m) n 0
    simp only [pow_zero, mul_one] at this
    exact le_trans this (hbnd m)
  calc |f.val m| * |(mapImageGen T₁ T₂ m).val n|
      ≤ |f.val m| * (K * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = K * (|f.val m| * (1 + (m : ℝ)) ^ S) := by ring

set_option maxHeartbeats 800000 in
/-- Bound on the mapped sum at each output index. -/
private theorem mapValGen_bound (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (f : RapidDecaySeq) (n k : ℕ) :
    |∑' m, f.val m * (mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
    (∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2)
      (mapImageGen T₁ T₂ m)) * ((1 + (n : ℝ)) ^ 2)⁻¹ := by
  have h_summ := mapInnerGen_abs_summable T₁ T₂ f n
  -- |tsum a_m| ≤ tsum |a_m| = tsum (|f m| * |Φ m n|)
  have h_abs : |∑' m, f.val m * (mapImageGen T₁ T₂ m).val n| ≤
      ∑' m, |f.val m| * |(mapImageGen T₁ T₂ m).val n| := by
    have h_norm_summ : Summable (fun m =>
        ‖f.val m * (mapImageGen T₁ T₂ m).val n‖) :=
      h_summ.congr (fun m => by rw [Real.norm_eq_abs, abs_mul])
    calc |∑' m, f.val m * (mapImageGen T₁ T₂ m).val n|
        = ‖∑' m, f.val m * (mapImageGen T₁ T₂ m).val n‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * (mapImageGen T₁ T₂ m).val n‖ :=
          norm_tsum_le_tsum_norm h_norm_summ
      _ = ∑' m, |f.val m| * |(mapImageGen T₁ T₂ m).val n| :=
          tsum_congr (fun m => by rw [Real.norm_eq_abs, abs_mul])
  -- Pointwise: |f m| * |Φ m n| * (1+n)^k ≤ |f m| * seminorm_{k+2}(Φ m) / (1+n)^2
  have h_pw : ∀ m, |f.val m| * |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
      |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) *
      ((1 + (n : ℝ)) ^ 2)⁻¹ := fun m => by
    have := mapImageGen_val_weight_bound T₁ T₂ m n k
    calc |f.val m| * |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k
        = |f.val m| * (|(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k) := by ring
      _ ≤ |f.val m| * (RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) *
          ((1 + (n : ℝ)) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  calc |∑' m, f.val m * (mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k
      ≤ (∑' m, |f.val m| * |(mapImageGen T₁ T₂ m).val n|) * (1 + (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right h_abs (by positivity)
    _ = ∑' m, |f.val m| * |(mapImageGen T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k :=
        (tsum_mul_right).symm
    _ ≤ ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) *
          ((1 + (n : ℝ)) ^ 2)⁻¹ :=
        (h_summ.mul_right _).tsum_le_tsum h_pw
          ((mapCoeffGen_seminorm_summable T₁ T₂ f (k + 2)).mul_right _)
    _ = _ := tsum_mul_right

/-- The mapped rapid decay sequence (general version). -/
private def mapRapidDecayGen (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (f : RapidDecaySeq) : RapidDecaySeq where
  val n := ∑' m, f.val m * (mapImageGen T₁ T₂ m).val n
  rapid_decay k :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (by positivity))
      (fun n => mapValGen_bound T₁ T₂ f n k)
      (NuclearTensorProduct.summable_inv_one_add_sq.mul_left _)

set_option maxHeartbeats 800000 in
/-- Seminorm bound: `seminorm_k(map f) ≤ K · seminorm_S(f)`. -/
private theorem mapRapidDecayGen_seminorm_bound (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂)
    (k : ℕ) : ∃ K > 0, ∃ S : ℕ, ∀ (f : RapidDecaySeq),
    RapidDecaySeq.rapidDecaySeminorm k (mapRapidDecayGen T₁ T₂ f) ≤
    K * RapidDecaySeq.rapidDecaySeminorm S f := by
  classical
  obtain ⟨K', hK', S, hbnd⟩ := mapImageGen_seminorm_bound T₁ T₂ (k + 2)
  set T := ∑' n : ℕ, ((1 + (n : ℝ)) ^ 2)⁻¹
  have hT_pos : 0 < T := NuclearTensorProduct.summable_inv_one_add_sq.tsum_pos
    (fun n => by positivity) 0 (by positivity)
  refine ⟨K' * T, by positivity, S, fun f => ?_⟩
  show ∑' n, |(mapRapidDecayGen T₁ T₂ f).val n| * (1 + (n : ℝ)) ^ k ≤
    K' * T * RapidDecaySeq.rapidDecaySeminorm S f
  set B := ∑' m, |f.val m| *
    RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImageGen T₁ T₂ m) with hB_def
  have hdom : Summable (fun m => |f.val m| * (K' * (1 + (m : ℝ)) ^ S)) :=
    ((f.rapid_decay S).mul_left K').congr (fun m => by ring)
  have hB_le : B ≤ K' * RapidDecaySeq.rapidDecaySeminorm S f := by
    calc B ≤ ∑' m, |f.val m| * (K' * (1 + (m : ℝ)) ^ S) :=
            (mapCoeffGen_seminorm_summable T₁ T₂ f (k + 2)).tsum_le_tsum
              (fun m => mul_le_mul_of_nonneg_left (hbnd m) (abs_nonneg _)) hdom
      _ = K' * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ S := by
            rw [← tsum_mul_left]; congr 1; ext m; ring
  calc ∑' (n : ℕ), |(mapRapidDecayGen T₁ T₂ f).val n| * (1 + (n : ℝ)) ^ k
      ≤ ∑' (n : ℕ), B * ((1 + (n : ℝ)) ^ 2)⁻¹ :=
        ((mapRapidDecayGen T₁ T₂ f).rapid_decay k).tsum_le_tsum
          (fun n => mapValGen_bound T₁ T₂ f n k)
          (NuclearTensorProduct.summable_inv_one_add_sq.mul_left B)
    _ = B * T := tsum_mul_left
    _ ≤ K' * RapidDecaySeq.rapidDecaySeminorm S f * T :=
        mul_le_mul_of_nonneg_right hB_le (le_of_lt hT_pos)
    _ = K' * T * RapidDecaySeq.rapidDecaySeminorm S f := by ring

set_option maxHeartbeats 400000 in
/-- The map as a linear map on RapidDecaySeq. -/
private def mapLMGen (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) :
    NuclearTensorProduct E₁ E₂ →ₗ[ℝ] NuclearTensorProduct F₁ F₂ where
  toFun := mapRapidDecayGen T₁ T₂
  map_add' f g := by
    ext n
    show (mapRapidDecayGen T₁ T₂ (f + g)).val n =
      ((mapRapidDecayGen T₁ T₂ f) + (mapRapidDecayGen T₁ T₂ g)).val n
    simp only [mapRapidDecayGen, RapidDecaySeq.add_val]
    -- Goal: ∑' m, (f+g).val m * Φ(m).val n = ∑' m, f.val m * ... + ∑' m, g.val m * ...
    -- (f+g).val m is definitionally f.val m + g.val m, so the LHS summand
    -- is (f.val m + g.val m) * Φ(m).val n = f.val m * ... + g.val m * ...
    have h_eq : (fun m => (f + g).val m * (mapImageGen T₁ T₂ m).val n) =
      (fun m => f.val m * (mapImageGen T₁ T₂ m).val n +
                g.val m * (mapImageGen T₁ T₂ m).val n) := by
      ext m; show (f.val m + g.val m) * _ = _; ring
    rw [h_eq]
    exact (mapInnerGen_summable T₁ T₂ f n).tsum_add (mapInnerGen_summable T₁ T₂ g n)
  map_smul' r f := by
    ext n
    show (mapRapidDecayGen T₁ T₂ (r • f)).val n =
      (r • (mapRapidDecayGen T₁ T₂ f)).val n
    simp only [mapRapidDecayGen, RapidDecaySeq.smul_val]
    -- Goal: ∑' m, (r•f).val m * Φ(m).val n = r * ∑' m, f.val m * ...
    -- (r•f).val m is definitionally r * f.val m
    have h_eq : (fun m => (r • f).val m * (mapImageGen T₁ T₂ m).val n) =
      (fun m => r • (f.val m * (mapImageGen T₁ T₂ m).val n)) := by
      ext m; show r * f.val m * _ = r • _; rw [smul_eq_mul]; ring
    rw [h_eq]
    exact (mapInnerGen_summable T₁ T₂ f n).tsum_const_smul r

set_option maxHeartbeats 800000 in
/-- Norm-summability of `c_{E}(m,f) * c_{F}(n, T(ψ^E_m))`: the coefficient product series
converges absolutely, using coeff_decay + CLM continuity + basis_growth.
This is the cross-type version of `norm_summable_coeff_comp_CLM`. -/
private theorem norm_summable_coeff_comp_CLM_general
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [DyninMityaginSpace F]
    (T : E →L[ℝ] F) (f : E) (n : ℕ) :
    Summable (fun m => ‖DyninMityaginSpace.coeff (E := E) m f *
      DyninMityaginSpace.coeff (E := F) n (T (DyninMityaginSpace.basis (E := E) m))‖) := by
  classical
  simp only [Real.norm_eq_abs, abs_mul]
  -- Step 1: Bound |coeff^F n (T(ψ^E_m))| ≤ K * (1+m)^S
  obtain ⟨C₀, hC₀, s₀, hdecay₀⟩ := DyninMityaginSpace.coeff_decay (E := F) 0
  have hT_cont : Continuous ((s₀.sup DyninMityaginSpace.p).comp T.toLinearMap) := by
    apply Continuous.comp _ T.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₀)
    show Continuous fun (x : F) =>
      (Seminorm.coeFnAddMonoidHom ℝ F) (∑ i ∈ s₀, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  obtain ⟨t, Dnn, hDnn, hle⟩ := Seminorm.bound_of_continuous
    DyninMityaginSpace.h_with _ hT_cont
  obtain ⟨D, hD, S, hbasis⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p t DyninMityaginSpace.basis
    (fun i _ => DyninMityaginSpace.basis_growth i)
  have h_image : ∀ m, |DyninMityaginSpace.coeff (E := F) n
      (T (DyninMityaginSpace.basis (E := E) m))| ≤
      C₀ * ↑Dnn * D * (1 + (m : ℝ)) ^ S := by
    intro m
    calc |DyninMityaginSpace.coeff (E := F) n
          (T (DyninMityaginSpace.basis (E := E) m))|
        ≤ C₀ * (s₀.sup DyninMityaginSpace.p)
            (T (DyninMityaginSpace.basis (E := E) m)) := by
          have := hdecay₀ (T (DyninMityaginSpace.basis (E := E) m)) n
          simp only [pow_zero, mul_one] at this; exact this
      _ ≤ C₀ * (↑Dnn * (t.sup DyninMityaginSpace.p)
            (DyninMityaginSpace.basis (E := E) m)) := by
          gcongr; have := hle (DyninMityaginSpace.basis (E := E) m)
          simp only [Seminorm.comp_apply] at this; exact this
      _ ≤ C₀ * (↑Dnn * (D * (1 + (m : ℝ)) ^ S)) := by gcongr; exact hbasis m
      _ = C₀ * ↑Dnn * D * (1 + (m : ℝ)) ^ S := by ring
  -- Step 2: Combine with coeff_decay at S+2 to get 1/(1+m)^2 decay
  obtain ⟨C_d, hC_d, s_d, hdecay_d⟩ := DyninMityaginSpace.coeff_decay (E := E) (S + 2)
  set K := C₀ * ↑Dnn * D * C_d * (s_d.sup DyninMityaginSpace.p) f
  apply Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    (NuclearTensorProduct.summable_inv_one_add_sq.mul_left K)
  have hm_pos : (0 : ℝ) < 1 + (m : ℝ) := by positivity
  have h_sq_pos : (0 : ℝ) < (1 + (m : ℝ)) ^ 2 := pow_pos hm_pos 2
  have h_d' : |DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ S ≤
      C_d * (s_d.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
    have h_eq : |DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ S =
        |DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ (S + 2) *
        ((1 + (m : ℝ)) ^ 2)⁻¹ := by rw [pow_add]; field_simp
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right (hdecay_d f m) (inv_nonneg.mpr h_sq_pos.le)
  calc |DyninMityaginSpace.coeff (E := E) m f| *
      |DyninMityaginSpace.coeff (E := F) n
        (T (DyninMityaginSpace.basis (E := E) m))|
      ≤ |DyninMityaginSpace.coeff (E := E) m f| *
          (C₀ * ↑Dnn * D * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left (h_image m) (abs_nonneg _)
    _ = C₀ * ↑Dnn * D *
          (|DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ S) := by ring
    _ ≤ C₀ * ↑Dnn * D * (C_d * (s_d.sup DyninMityaginSpace.p) f *
        ((1 + (m : ℝ)) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left h_d' (by positivity)
    _ = K * ((1 + (m : ℝ)) ^ 2)⁻¹ := by ring

end GeneralMapCLM

/-! ## Main definitions and theorems -/

set_option maxHeartbeats 1200000 in
/-- **Generalized tensor product of CLMs** between different NTP spaces.

Given `T₁ : E₁ →L[ℝ] F₁` and `T₂ : E₂ →L[ℝ] F₂`, the tensor product
`T₁ ⊗ T₂ : NTP(E₁, E₂) →L[ℝ] NTP(F₁, F₂)` maps basis vectors by
`basisVec(a,b) ↦ pure(T₁ ψ_a, T₂ ψ_b)` and extends by continuity.

The proof follows the same structure as `nuclearTensorProduct_mapCLM`:
1. Define the action on basis vectors via `mapImageGen`
2. Show polynomial growth of seminorms (`mapImageGen_seminorm_bound`)
3. Show the induced map on rapid-decay sequences is continuous -/
def nuclearTensorProduct_mapCLM_general
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    {F₁ : Type*} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
    [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [DyninMityaginSpace F₁]
    {F₂ : Type*} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
    [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [DyninMityaginSpace F₂]
    (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct F₁ F₂ :=
  { mapLMGen T₁ T₂ with
    cont := by
      apply WithSeminorms.continuous_of_isBounded
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct F₁ F₂)))
      intro k
      obtain ⟨K, hK, S, hbound⟩ := mapRapidDecayGen_seminorm_bound T₁ T₂ k
      refine ⟨{S}, ⟨K, le_of_lt hK⟩, fun f => ?_⟩
      simp only [Finset.sup_singleton, Seminorm.comp_apply, mapLMGen]
      exact hbound f }

set_option maxHeartbeats 1600000 in
/-- **`mapCLM_general` acts on pure tensors by applying each factor.**
`(T₁ ⊗ T₂)(pure e₁ e₂) = pure (T₁ e₁) (T₂ e₂)` -/
theorem nuclearTensorProduct_mapCLM_general_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    {F₁ : Type*} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
    [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [DyninMityaginSpace F₁]
    {F₂ : Type*} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
    [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [DyninMityaginSpace F₂]
    (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_mapCLM_general T₁ T₂ (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure (T₁ e₁) (T₂ e₂) := by
  ext n
  show (mapRapidDecayGen T₁ T₂ (pure e₁ e₂)).val n = (pure (T₁ e₁) (T₂ e₂)).val n
  simp only [mapRapidDecayGen, pure_val, mapImageGen]
  set a' := (Nat.unpair n).1
  set b' := (Nat.unpair n).2
  -- Abbreviations
  set c_E₁ := DyninMityaginSpace.coeff (E := E₁)
  set c_E₂ := DyninMityaginSpace.coeff (E := E₂)
  set c_F₁ := DyninMityaginSpace.coeff (E := F₁)
  set c_F₂ := DyninMityaginSpace.coeff (E := F₂)
  set ψ₁ := DyninMityaginSpace.basis (E := E₁)
  set ψ₂ := DyninMityaginSpace.basis (E := E₂)
  -- The two factor sequences
  set f₁ : ℕ → ℝ := fun i => c_E₁ i e₁ * c_F₁ a' (T₁ (ψ₁ i))
  set f₂ : ℕ → ℝ := fun j => c_E₂ j e₂ * c_F₂ b' (T₂ (ψ₂ j))
  -- Step 1: Norm-summability from the cross-type helper lemma
  have hsumm₁ : Summable (fun i => ‖f₁ i‖) :=
    norm_summable_coeff_comp_CLM_general T₁ e₁ a'
  have hsumm₂ : Summable (fun j => ‖f₂ j‖) :=
    norm_summable_coeff_comp_CLM_general T₂ e₂ b'
  -- Step 2: DM expansion gives the tsum formulas
  have h_exp₁ : c_F₁ a' (T₁ e₁) = ∑' i, f₁ i :=
    DyninMityaginSpace.expansion ((c_F₁ a').comp T₁) e₁
  have h_exp₂ : c_F₂ b' (T₂ e₂) = ∑' j, f₂ j :=
    DyninMityaginSpace.expansion ((c_F₂ b').comp T₂) e₂
  -- Step 3: Chain the equalities (RHS → product → double sum → single sum → LHS)
  symm
  calc c_F₁ a' (T₁ e₁) * c_F₂ b' (T₂ e₂)
      = (∑' i, f₁ i) * (∑' j, f₂ j) := by rw [h_exp₁, h_exp₂]
    _ = ∑' (p : ℕ × ℕ), f₁ p.1 * f₂ p.2 :=
        tsum_mul_tsum_of_summable_norm hsumm₁ hsumm₂
    _ = ∑' m, f₁ (Nat.unpair m).1 * f₂ (Nat.unpair m).2 :=
        (Equiv.tsum_eq Nat.pairEquiv.symm _).symm
    _ = ∑' m, (c_E₁ (Nat.unpair m).1 e₁ * c_E₂ (Nat.unpair m).2 e₂) *
          (c_F₁ a' (T₁ (ψ₁ (Nat.unpair m).1)) *
           c_F₂ b' (T₂ (ψ₂ (Nat.unpair m).2))) := by
        congr 1; ext m; simp only [f₁, f₂]; ring

end GaussianField

end
