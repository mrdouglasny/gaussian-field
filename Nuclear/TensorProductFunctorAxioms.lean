/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Tensor Product Functor

Theorems for the functorial structure of the nuclear tensor product:
CLMs on nuclear Fréchet spaces lift to CLMs on the completed projective
tensor product, preserving composition and identity.

## Main definitions

- `nuclearTensorProduct_mapCLM` — `T₁ ⊗ T₂` on `NuclearTensorProduct`

## Main theorems

- `nuclearTensorProduct_mapCLM_pure` — action on pure tensors
- `nuclearTensorProduct_mapCLM_comp` — functoriality
- `nuclearTensorProduct_mapCLM_id` — identity preservation
- `nuclearTensorProduct_swapCLM` — swap factors
- `nuclearTensorProduct_swapCLM_pure` — swap on pure tensors

## References

- Trèves, *Topological Vector Spaces, Distributions, and Kernels*, Ch. 43, 50
-/

import Nuclear.NuclearTensorProduct

noncomputable section

namespace GaussianField

open NuclearTensorProduct

/-! ## Swap implementation -/

/-- Swap the components of a Cantor pair index. -/
private def pairSwap (m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair m).2 (Nat.unpair m).1

private theorem pairSwap_involutive : Function.Involutive pairSwap := fun m => by
  show Nat.pair (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).2
    (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).1 = m
  rw [Nat.unpair_pair]
  exact Nat.pair_unpair m

private def pairSwapEquiv : ℕ ≃ ℕ :=
  pairSwap_involutive.toPerm pairSwap

@[simp] private theorem pairSwapEquiv_apply (m : ℕ) :
    pairSwapEquiv m = pairSwap m :=
  congr_fun pairSwap_involutive.coe_toPerm m

private theorem one_add_le_sq_pairSwap (m : ℕ) :
    (1 + (m : ℝ)) ≤ 4 * (1 + (pairSwap m : ℝ)) ^ 2 := by
  set a := (Nat.unpair m).1
  set b := (Nat.unpair m).2
  have hm : m = Nat.pair a b := (Nat.pair_unpair m).symm
  have h_sw : pairSwap m = Nat.pair b a := rfl
  have ha : (a : ℝ) ≤ pairSwap m := by
    rw [h_sw]; exact_mod_cast Nat.right_le_pair b a
  have hb : (b : ℝ) ≤ pairSwap m := by
    rw [h_sw]; exact_mod_cast Nat.left_le_pair b a
  have h_bnd : (m : ℝ) ≤ ((a : ℝ) + (b : ℝ) + 1) ^ 2 := by
    rw [hm]; exact_mod_cast nat_pair_bound a b
  nlinarith

private def swapRapidDecay (f : RapidDecaySeq) : RapidDecaySeq where
  val m := f.val (pairSwap m)
  rapid_decay k := by
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg m k)
    · intro m
      have h_wt : (1 + (m : ℝ)) ^ k ≤ (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) :=
        calc (1 + (m : ℝ)) ^ k
            ≤ (4 * (1 + (pairSwap m : ℝ)) ^ 2) ^ k :=
              pow_le_pow_left₀ (by positivity) (one_add_le_sq_pairSwap m) k
          _ = (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
      show |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
        (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))
      nlinarith [abs_nonneg (f.val (pairSwap m))]
    · have h_eq : (fun m => (4 : ℝ) ^ k *
          (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) =
          fun m => (4 : ℝ) ^ k *
          ((fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k)) (pairSwapEquiv m)) := by
        ext m; simp [pairSwapEquiv_apply]
      rw [h_eq]
      exact (pairSwapEquiv.summable_iff.mpr (f.rapid_decay (2 * k))).const_smul ((4 : ℝ) ^ k)

set_option maxHeartbeats 400000 in
private theorem swap_seminorm_bound (k : ℕ) (f : RapidDecaySeq) :
    RapidDecaySeq.rapidDecaySeminorm k (swapRapidDecay f) ≤
    (4 : ℝ) ^ k * RapidDecaySeq.rapidDecaySeminorm (2 * k) f := by
  show ∑' m, |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
    (4 : ℝ) ^ k * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ (2 * k)
  have h_reindex : ∑' m, |f.val m| * (1 + (m : ℝ)) ^ (2 * k) =
      ∑' m, |f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by
    have := (pairSwapEquiv.tsum_eq
      (fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k))).symm
    simp only [pairSwapEquiv_apply] at this; exact this
  rw [h_reindex, ← tsum_mul_left]
  have h_term : ∀ m, |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
      (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k)) := by
    intro m
    have h_wt : (1 + (m : ℝ)) ^ k ≤ (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) :=
      calc (1 + (m : ℝ)) ^ k
          ≤ (4 * (1 + (pairSwap m : ℝ)) ^ 2) ^ k :=
            pow_le_pow_left₀ (by positivity) (one_add_le_sq_pairSwap m) k
        _ = (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    nlinarith [abs_nonneg (f.val (pairSwap m))]
  have h_sum : Summable (fun m => (4 : ℝ) ^ k *
      (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) := by
    have h_eq : (fun m => (4 : ℝ) ^ k *
        (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) =
        fun m => (4 : ℝ) ^ k *
        ((fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k)) (pairSwapEquiv m)) := by
      ext m; simp [pairSwapEquiv_apply]
    rw [h_eq]
    exact (pairSwapEquiv.summable_iff.mpr (f.rapid_decay (2 * k))).const_smul ((4 : ℝ) ^ k)
  exact ((swapRapidDecay f).rapid_decay k).tsum_le_tsum h_term h_sum

private def swapLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    NuclearTensorProduct E₁ E₂ →ₗ[ℝ] NuclearTensorProduct E₂ E₁ where
  toFun := swapRapidDecay
  map_add' := fun f g => by ext m; rfl
  map_smul' := fun r f => by ext m; rfl

def nuclearTensorProduct_swapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₂ E₁ :=
  { swapLM with
    cont := by
      apply WithSeminorms.continuous_of_isBounded
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₂ E₁)))
      intro k
      refine ⟨{2 * k}, ⟨(4 : ℝ) ^ k, by positivity⟩, fun f => ?_⟩
      simp only [Finset.sup_singleton, Seminorm.comp_apply]
      exact swap_seminorm_bound k f }

theorem nuclearTensorProduct_swapCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_swapCLM (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure e₂ e₁ := by
  ext m
  show (NuclearTensorProduct.pure e₁ e₂).val (pairSwap m) =
    (NuclearTensorProduct.pure e₂ e₁).val m
  simp only [pure_val, pairSwap, Nat.unpair_pair]; ring

set_option maxHeartbeats 800000 in
/-- **evalCLM commutes with swap.**

For `E₁ = E₂ = E` (same DyninMityaginSpace on both factors):
  `evalCLM φ₁ φ₂ (swapCLM f) = evalCLM φ₂ φ₁ f`

Proof: Unfold `evalCLM` to its `lift` tsum, substitute the swap, relabel by `pairSwapEquiv`,
and use `mul_comm` on the `φ₁(ψ_a) * φ₂(ψ_b)` factors. -/
theorem evalCLM_comp_swapCLM
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    (φ₁ φ₂ : E →L[ℝ] ℝ) (f : NuclearTensorProduct E E) :
    NuclearTensorProduct.evalCLM φ₁ φ₂ (nuclearTensorProduct_swapCLM f) =
    NuclearTensorProduct.evalCLM φ₂ φ₁ f := by
  -- Both sides unfold to tsums via the lift definition of evalCLM.
  -- evalCLM φ₁ φ₂ a = ∑' m, a.val m • compBilin φ₁ φ₂ (basis a') (basis b')
  -- where (a',b') = unpair(m), and compBilin φ₁ φ₂ e₁ e₂ = φ₁ e₁ * φ₂ e₂ (rfl).
  set ψ := DyninMityaginSpace.basis (E := E)
  -- Unfold evalCLM to its lift/tsum definition (compBilin_apply is rfl)
  show (∑' m, (nuclearTensorProduct_swapCLM f).val m *
      (φ₁ (ψ (Nat.unpair m).1) * φ₂ (ψ (Nat.unpair m).2))) =
    ∑' m, f.val m * (φ₂ (ψ (Nat.unpair m).1) * φ₁ (ψ (Nat.unpair m).2))
  -- LHS: (swapCLM f).val m = f.val(pairSwap m) by definition of swapRapidDecay
  -- Set h to be the LHS summand
  set h := fun m => f.val (pairSwap m) *
    (φ₁ (ψ (Nat.unpair m).1) * φ₂ (ψ (Nat.unpair m).2))
  -- The LHS tsum equals ∑' m, h m
  have h_lhs_eq : ∀ m, (nuclearTensorProduct_swapCLM f).val m *
      (φ₁ (ψ (Nat.unpair m).1) * φ₂ (ψ (Nat.unpair m).2)) = h m := fun _ => rfl
  simp_rw [h_lhs_eq]
  -- Relabel: ∑' m, h m = ∑' m, h(pairSwap m) via pairSwapEquiv
  rw [(pairSwapEquiv.tsum_eq h).symm]
  -- h(pairSwap m) = f.val(pairSwap(pairSwap m)) * (φ₁(ψ (unpair(pairSwap m)).1) * φ₂(ψ (unpair(pairSwap m)).2))
  --              = f.val m * (φ₁(ψ (unpair m).2) * φ₂(ψ (unpair m).1))
  -- since pairSwap is involutive and pairSwap m = pair (unpair m).2 (unpair m).1
  simp only [pairSwapEquiv_apply, h]
  congr 1; ext m
  rw [pairSwap_involutive m]
  simp only [pairSwap, Nat.unpair_pair]
  ring

/-! ## Tensor product of CLMs

The key construction: `mapCLM T₁ T₂` acts on `f : NTP E₁ E₂ = RapidDecaySeq` by
mapping each basis vector `basisVec m ↦ pure(T₁(ψ_a), T₂(ψ_b))` where `(a,b) = unpair(m)`.

At the coefficient level:
`(mapCLM T₁ T₂ f).val n = ∑' m, f.val m · coeff a'(T₁(ψ_a)) · coeff b'(T₂(ψ_b))`
where `(a,b) = unpair(m)`, `(a',b') = unpair(n)`.

Convergence uses `coeff_decay` (a' decay) and `basis_growth` (a growth from CLM),
with rapid decay of f absorbing the polynomial growth. -/

section MapCLM

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]

/-- The image of basis vector `m` under `T₁ ⊗ T₂`:
`Φ(m) = pure(T₁(ψ_a), T₂(ψ_b))` where `(a,b) = unpair(m)`. -/
def mapImage (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) (m : ℕ) :
    NuclearTensorProduct E₁ E₂ :=
  NuclearTensorProduct.pure
    (T₁ (DyninMityaginSpace.basis (Nat.unpair m).1))
    (T₂ (DyninMityaginSpace.basis (Nat.unpair m).2))

/-- Pointwise bound: `|(g m).val n| * (1+n)^j ≤ seminorm_j(g m)`. -/
theorem val_le_seminorm (g : RapidDecaySeq) (n j : ℕ) :
    |g.val n| * (1 + (n : ℝ)) ^ j ≤ RapidDecaySeq.rapidDecaySeminorm j g :=
  (g.rapid_decay j).le_tsum n (fun k _ => mul_nonneg (abs_nonneg _) (by positivity))

/-- Polynomial bound on seminorms of `mapImage`.
`seminorm_k(Φ(m)) ≤ K * (1+m)^S`. -/
theorem mapImage_seminorm_bound (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) (k : ℕ) :
    ∃ K > 0, ∃ S : ℕ, ∀ m,
    RapidDecaySeq.rapidDecaySeminorm k (mapImage T₁ T₂ m) ≤ K * (1 + (m : ℝ)) ^ S := by
  classical
  obtain ⟨C, s₁, s₂, hpure⟩ := pure_seminorm_bound (E₁ := E₁) (E₂ := E₂) k
  -- Bound (s₁.sup p)(T₁(basis a)) via CLM continuity + basis_growth
  have hT₁_cont : Continuous ((s₁.sup DyninMityaginSpace.p).comp T₁.toLinearMap) := by
    apply Continuous.comp _ T₁.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₁)
    show Continuous fun (x : E₁) =>
      (Seminorm.coeFnAddMonoidHom ℝ E₁) (∑ i ∈ s₁, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  obtain ⟨t₁, C₁nn, hC₁nn, hle₁⟩ := Seminorm.bound_of_continuous
    DyninMityaginSpace.h_with _ hT₁_cont
  have hT₂_cont : Continuous ((s₂.sup DyninMityaginSpace.p).comp T₂.toLinearMap) := by
    apply Continuous.comp _ T₂.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₂)
    show Continuous fun (x : E₂) =>
      (Seminorm.coeFnAddMonoidHom ℝ E₂) (∑ i ∈ s₂, DyninMityaginSpace.p i) x
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
  calc RapidDecaySeq.rapidDecaySeminorm k (mapImage T₁ T₂ m)
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
private theorem mapInner_summable (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : RapidDecaySeq) (n : ℕ) :
    Summable (fun m => f.val m * (mapImage T₁ T₂ m).val n) := by
  classical
  obtain ⟨K, hK, S, hbnd⟩ := mapImage_seminorm_bound T₁ T₂ 0
  refine Summable.of_norm_bounded ((f.rapid_decay S).mul_left K) (fun m => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |(mapImage T₁ T₂ m).val n| ≤ K * (1 + (m : ℝ)) ^ S := by
    have := val_le_seminorm (mapImage T₁ T₂ m) n 0
    simp only [pow_zero, mul_one] at this
    exact le_trans this (hbnd m)
  calc |f.val m| * |(mapImage T₁ T₂ m).val n|
      ≤ |f.val m| * (K * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = K * (|f.val m| * (1 + (m : ℝ)) ^ S) := by ring

/-- Summability of `∑ₘ |fₘ| * seminorm_k(Φ(m))` using polynomial bound on Φ. -/
private theorem mapCoeff_seminorm_summable (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : RapidDecaySeq) (k : ℕ) :
    Summable (fun m => |f.val m| *
      RapidDecaySeq.rapidDecaySeminorm k (mapImage T₁ T₂ m)) := by
  classical
  obtain ⟨K, hK, S, hbnd⟩ := mapImage_seminorm_bound T₁ T₂ k
  exact Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun m => mul_le_mul_of_nonneg_left (hbnd m) (abs_nonneg _))
    (((f.rapid_decay S).mul_left K).congr (fun m => by ring))

/-- Pointwise bound on the mapped value times weight:
`|Φ(m).val n| * (1+n)^k ≤ seminorm_{k+2}(Φ(m)) / (1+n)^2`. -/
private theorem mapImage_val_weight_bound (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (m n k : ℕ) :
    |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
    RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) *
      ((1 + (n : ℝ)) ^ 2)⁻¹ := by
  have hn_pos : (0 : ℝ) < 1 + (n : ℝ) := by positivity
  rw [le_mul_inv_iff₀ (pow_pos hn_pos 2)]
  calc |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k * (1 + (n : ℝ)) ^ 2
      = |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ (k + 2) := by rw [pow_add]; ring
    _ ≤ RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) :=
        val_le_seminorm _ n (k + 2)

/-- Summability of the absolute-value series for mapCLM. -/
private theorem mapInner_abs_summable (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : RapidDecaySeq) (n : ℕ) :
    Summable (fun m => |f.val m| * |(mapImage T₁ T₂ m).val n|) := by
  classical
  obtain ⟨K, _, S, hbnd⟩ := mapImage_seminorm_bound T₁ T₂ 0
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
    ((f.rapid_decay S).mul_left K)
  have h1 : |(mapImage T₁ T₂ m).val n| ≤ K * (1 + (m : ℝ)) ^ S := by
    have := val_le_seminorm (mapImage T₁ T₂ m) n 0
    simp only [pow_zero, mul_one] at this
    exact le_trans this (hbnd m)
  calc |f.val m| * |(mapImage T₁ T₂ m).val n|
      ≤ |f.val m| * (K * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = K * (|f.val m| * (1 + (m : ℝ)) ^ S) := by ring

set_option maxHeartbeats 800000 in
/-- Bound on the mapped sum at each output index. -/
private theorem mapVal_bound (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : RapidDecaySeq) (n k : ℕ) :
    |∑' m, f.val m * (mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
    (∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2)
      (mapImage T₁ T₂ m)) * ((1 + (n : ℝ)) ^ 2)⁻¹ := by
  have h_summ := mapInner_abs_summable T₁ T₂ f n
  -- |tsum a_m| ≤ tsum |a_m| = tsum (|f m| * |Φ m n|)
  have h_abs : |∑' m, f.val m * (mapImage T₁ T₂ m).val n| ≤
      ∑' m, |f.val m| * |(mapImage T₁ T₂ m).val n| := by
    have h_norm_summ : Summable (fun m =>
        ‖f.val m * (mapImage T₁ T₂ m).val n‖) :=
      h_summ.congr (fun m => by rw [Real.norm_eq_abs, abs_mul])
    calc |∑' m, f.val m * (mapImage T₁ T₂ m).val n|
        = ‖∑' m, f.val m * (mapImage T₁ T₂ m).val n‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' m, ‖f.val m * (mapImage T₁ T₂ m).val n‖ :=
          norm_tsum_le_tsum_norm h_norm_summ
      _ = ∑' m, |f.val m| * |(mapImage T₁ T₂ m).val n| :=
          tsum_congr (fun m => by rw [Real.norm_eq_abs, abs_mul])
  -- Pointwise: |f m| * |Φ m n| * (1+n)^k ≤ |f m| * seminorm_{k+2}(Φ m) / (1+n)^2
  have h_pw : ∀ m, |f.val m| * |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k ≤
      |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) *
      ((1 + (n : ℝ)) ^ 2)⁻¹ := fun m => by
    have := mapImage_val_weight_bound T₁ T₂ m n k
    calc |f.val m| * |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k
        = |f.val m| * (|(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k) := by ring
      _ ≤ |f.val m| * (RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) *
          ((1 + (n : ℝ)) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  calc |∑' m, f.val m * (mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k
      ≤ (∑' m, |f.val m| * |(mapImage T₁ T₂ m).val n|) * (1 + (n : ℝ)) ^ k :=
        mul_le_mul_of_nonneg_right h_abs (by positivity)
    _ = ∑' m, |f.val m| * |(mapImage T₁ T₂ m).val n| * (1 + (n : ℝ)) ^ k :=
        (tsum_mul_right).symm
    _ ≤ ∑' m, |f.val m| * RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) *
          ((1 + (n : ℝ)) ^ 2)⁻¹ :=
        (h_summ.mul_right _).tsum_le_tsum h_pw
          ((mapCoeff_seminorm_summable T₁ T₂ f (k + 2)).mul_right _)
    _ = _ := tsum_mul_right

/-- The mapped rapid decay sequence. -/
private def mapRapidDecay (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : RapidDecaySeq) : RapidDecaySeq where
  val n := ∑' m, f.val m * (mapImage T₁ T₂ m).val n
  rapid_decay k :=
    Summable.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (by positivity))
      (fun n => mapVal_bound T₁ T₂ f n k)
      (NuclearTensorProduct.summable_inv_one_add_sq.mul_left _)

set_option maxHeartbeats 800000 in
/-- Seminorm bound: `seminorm_k(map f) ≤ K · seminorm_S(f)`. -/
private theorem mapRapidDecay_seminorm_bound (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (k : ℕ) : ∃ K > 0, ∃ S : ℕ, ∀ (f : RapidDecaySeq),
    RapidDecaySeq.rapidDecaySeminorm k (mapRapidDecay T₁ T₂ f) ≤
    K * RapidDecaySeq.rapidDecaySeminorm S f := by
  classical
  obtain ⟨K', hK', S, hbnd⟩ := mapImage_seminorm_bound T₁ T₂ (k + 2)
  set T := ∑' n : ℕ, ((1 + (n : ℝ)) ^ 2)⁻¹
  have hT_pos : 0 < T := NuclearTensorProduct.summable_inv_one_add_sq.tsum_pos
    (fun n => by positivity) 0 (by positivity)
  refine ⟨K' * T, by positivity, S, fun f => ?_⟩
  show ∑' n, |(mapRapidDecay T₁ T₂ f).val n| * (1 + (n : ℝ)) ^ k ≤
    K' * T * RapidDecaySeq.rapidDecaySeminorm S f
  set B := ∑' m, |f.val m| *
    RapidDecaySeq.rapidDecaySeminorm (k + 2) (mapImage T₁ T₂ m) with hB_def
  have hdom : Summable (fun m => |f.val m| * (K' * (1 + (m : ℝ)) ^ S)) :=
    ((f.rapid_decay S).mul_left K').congr (fun m => by ring)
  have hB_le : B ≤ K' * RapidDecaySeq.rapidDecaySeminorm S f := by
    calc B ≤ ∑' m, |f.val m| * (K' * (1 + (m : ℝ)) ^ S) :=
            (mapCoeff_seminorm_summable T₁ T₂ f (k + 2)).tsum_le_tsum
              (fun m => mul_le_mul_of_nonneg_left (hbnd m) (abs_nonneg _)) hdom
      _ = K' * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ S := by
            rw [← tsum_mul_left]; congr 1; ext m; ring
  calc ∑' (n : ℕ), |(mapRapidDecay T₁ T₂ f).val n| * (1 + (n : ℝ)) ^ k
      ≤ ∑' (n : ℕ), B * ((1 + (n : ℝ)) ^ 2)⁻¹ :=
        ((mapRapidDecay T₁ T₂ f).rapid_decay k).tsum_le_tsum
          (fun n => mapVal_bound T₁ T₂ f n k)
          (NuclearTensorProduct.summable_inv_one_add_sq.mul_left B)
    _ = B * T := tsum_mul_left
    _ ≤ K' * RapidDecaySeq.rapidDecaySeminorm S f * T :=
        mul_le_mul_of_nonneg_right hB_le (le_of_lt hT_pos)
    _ = K' * T * RapidDecaySeq.rapidDecaySeminorm S f := by ring

set_option maxHeartbeats 400000 in
/-- The map as a linear map on RapidDecaySeq. -/
private def mapLM (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) :
    RapidDecaySeq →ₗ[ℝ] RapidDecaySeq where
  toFun := mapRapidDecay T₁ T₂
  map_add' f g := by
    ext n; show ∑' m, (f + g).val m * _ = (mapRapidDecay T₁ T₂ f + mapRapidDecay T₁ T₂ g).val n
    simp only [RapidDecaySeq.add_val, add_mul, mapRapidDecay]
    exact (mapInner_summable T₁ T₂ f n).tsum_add (mapInner_summable T₁ T₂ g n)
  map_smul' r f := by
    ext n; show ∑' m, (r • f).val m * _ = (r • mapRapidDecay T₁ T₂ f).val n
    simp only [RapidDecaySeq.smul_val, mul_assoc, mapRapidDecay]
    exact (mapInner_summable T₁ T₂ f n).tsum_const_smul r

set_option maxHeartbeats 800000 in
/-- Norm-summability of `c(m,f) * c(n, T(ψ_m))`: the coefficient product series
converges absolutely, using coeff_decay + CLM continuity + basis_growth. -/
private theorem norm_summable_coeff_comp_CLM
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    (T : E →L[ℝ] E) (f : E) (n : ℕ) :
    Summable (fun m => ‖DyninMityaginSpace.coeff m f *
      DyninMityaginSpace.coeff n (T (DyninMityaginSpace.basis m))‖) := by
  classical
  simp only [Real.norm_eq_abs, abs_mul]
  -- Step 1: Bound |coeff n (T(ψ_m))| ≤ K * (1+m)^S
  obtain ⟨C₀, hC₀, s₀, hdecay₀⟩ := DyninMityaginSpace.coeff_decay (E := E) 0
  have hT_cont : Continuous ((s₀.sup DyninMityaginSpace.p).comp T.toLinearMap) := by
    apply Continuous.comp _ T.continuous
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum DyninMityaginSpace.p s₀)
    show Continuous fun (x : E) =>
      (Seminorm.coeFnAddMonoidHom ℝ E) (∑ i ∈ s₀, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finset_sum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  obtain ⟨t, Dnn, hDnn, hle⟩ := Seminorm.bound_of_continuous
    DyninMityaginSpace.h_with _ hT_cont
  obtain ⟨D, hD, S, hbasis⟩ := finset_sup_poly_bound
    DyninMityaginSpace.p t DyninMityaginSpace.basis
    (fun i _ => DyninMityaginSpace.basis_growth i)
  have h_image : ∀ m, |DyninMityaginSpace.coeff n (T (DyninMityaginSpace.basis m))| ≤
      C₀ * ↑Dnn * D * (1 + (m : ℝ)) ^ S := by
    intro m
    calc |DyninMityaginSpace.coeff n (T (DyninMityaginSpace.basis m))|
        ≤ C₀ * (s₀.sup DyninMityaginSpace.p) (T (DyninMityaginSpace.basis m)) := by
          have := hdecay₀ (T (DyninMityaginSpace.basis m)) n
          simp only [pow_zero, mul_one] at this; exact this
      _ ≤ C₀ * (↑Dnn * (t.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis m)) := by
          gcongr; have := hle (DyninMityaginSpace.basis m)
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
  -- Key step: bound |c m f| * (1+m)^S by C_d * sem f / (1+m)^2
  have h_d' : |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ S ≤
      C_d * (s_d.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
    have h_eq : |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ S =
        |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ (S + 2) *
        ((1 + (m : ℝ)) ^ 2)⁻¹ := by rw [pow_add]; field_simp
    rw [h_eq]
    exact mul_le_mul_of_nonneg_right (hdecay_d f m) (inv_nonneg.mpr h_sq_pos.le)
  calc |DyninMityaginSpace.coeff m f| *
      |DyninMityaginSpace.coeff n (T (DyninMityaginSpace.basis m))|
      ≤ |DyninMityaginSpace.coeff m f| * (C₀ * ↑Dnn * D * (1 + (m : ℝ)) ^ S) :=
        mul_le_mul_of_nonneg_left (h_image m) (abs_nonneg _)
    _ = C₀ * ↑Dnn * D * (|DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ S) := by ring
    _ ≤ C₀ * ↑Dnn * D * (C_d * (s_d.sup DyninMityaginSpace.p) f *
        ((1 + (m : ℝ)) ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left h_d' (by positivity)
    _ = K * ((1 + (m : ℝ)) ^ 2)⁻¹ := by ring

end MapCLM

/-! ## Main definitions and theorems -/

set_option maxHeartbeats 1200000 in
/-- **Tensor product of CLMs on nuclear spaces.**

Given CLMs `T₁ : E₁ →L[ℝ] E₁` and `T₂ : E₂ →L[ℝ] E₂`, their tensor product
`T₁ ⊗ T₂` acts on `NuclearTensorProduct E₁ E₂` by mapping basis vector `m`
to `pure(T₁(ψ_a), T₂(ψ_b))` and extending by linearity/continuity. -/
def nuclearTensorProduct_mapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₁ E₂ :=
  { mapLM T₁ T₂ with
    cont := by
      apply WithSeminorms.continuous_of_isBounded
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
      intro k
      obtain ⟨K, hK, S, hbound⟩ := mapRapidDecay_seminorm_bound T₁ T₂ k
      refine ⟨{S}, ⟨K, le_of_lt hK⟩, fun f => ?_⟩
      simp only [Finset.sup_singleton, Seminorm.comp_apply, mapLM]
      exact hbound f }

set_option maxHeartbeats 1600000 in
/-- **`mapCLM` acts on pure tensors by applying each factor.**
`(T₁ ⊗ T₂)(pure e₁ e₂) = pure (T₁ e₁) (T₂ e₂)` -/
theorem nuclearTensorProduct_mapCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_mapCLM T₁ T₂ (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure (T₁ e₁) (T₂ e₂) := by
  ext n
  show (mapRapidDecay T₁ T₂ (pure e₁ e₂)).val n = (pure (T₁ e₁) (T₂ e₂)).val n
  simp only [mapRapidDecay, pure_val, mapImage]
  set a' := (Nat.unpair n).1
  set b' := (Nat.unpair n).2
  -- Abbreviations
  set c₁ := DyninMityaginSpace.coeff (E := E₁)
  set c₂ := DyninMityaginSpace.coeff (E := E₂)
  set ψ₁ := DyninMityaginSpace.basis (E := E₁)
  set ψ₂ := DyninMityaginSpace.basis (E := E₂)
  -- The two factor sequences
  set f₁ : ℕ → ℝ := fun i => c₁ i e₁ * c₁ a' (T₁ (ψ₁ i))
  set f₂ : ℕ → ℝ := fun j => c₂ j e₂ * c₂ b' (T₂ (ψ₂ j))
  -- Step 1: Norm-summability from the helper lemma
  have hsumm₁ : Summable (fun i => ‖f₁ i‖) := norm_summable_coeff_comp_CLM T₁ e₁ a'
  have hsumm₂ : Summable (fun j => ‖f₂ j‖) := norm_summable_coeff_comp_CLM T₂ e₂ b'
  -- Step 2: DM expansion gives the tsum formulas
  have h_exp₁ : c₁ a' (T₁ e₁) = ∑' i, f₁ i :=
    DyninMityaginSpace.expansion ((c₁ a').comp T₁) e₁
  have h_exp₂ : c₂ b' (T₂ e₂) = ∑' j, f₂ j :=
    DyninMityaginSpace.expansion ((c₂ b').comp T₂) e₂
  -- Step 3: Chain the equalities (RHS → product → double sum → single sum → LHS)
  symm
  calc c₁ a' (T₁ e₁) * c₂ b' (T₂ e₂)
      = (∑' i, f₁ i) * (∑' j, f₂ j) := by rw [h_exp₁, h_exp₂]
    _ = ∑' (p : ℕ × ℕ), f₁ p.1 * f₂ p.2 :=
        tsum_mul_tsum_of_summable_norm hsumm₁ hsumm₂
    _ = ∑' m, f₁ (Nat.unpair m).1 * f₂ (Nat.unpair m).2 :=
        (Equiv.tsum_eq Nat.pairEquiv.symm _).symm
    _ = ∑' m, (c₁ (Nat.unpair m).1 e₁ * c₂ (Nat.unpair m).2 e₂) *
          (c₁ a' (T₁ (ψ₁ (Nat.unpair m).1)) *
           c₂ b' (T₂ (ψ₂ (Nat.unpair m).2))) := by
        congr 1; ext m; simp only [f₁, f₂]; ring

set_option maxHeartbeats 800000 in
/-- **`mapCLM` preserves identity: `id ⊗ id = id`.**
Requires biorthogonality so that `basisVec m = pure(ψ_a, ψ_b)`. -/
theorem nuclearTensorProduct_mapCLM_id
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    [DyninMityaginSpace.HasBiorthogonalBasis E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    [DyninMityaginSpace.HasBiorthogonalBasis E₂] :
    nuclearTensorProduct_mapCLM
      (ContinuousLinearMap.id ℝ E₁)
      (ContinuousLinearMap.id ℝ E₂) =
    ContinuousLinearMap.id ℝ (NuclearTensorProduct E₁ E₂) := by
  ext f n
  show (mapRapidDecay (ContinuousLinearMap.id ℝ E₁) (ContinuousLinearMap.id ℝ E₂)
    f).val n = f.val n
  simp only [mapRapidDecay, mapImage, ContinuousLinearMap.id_apply, pure_val]
  -- By biorthogonality: coeff a (ψ b) = δ_{ab}, so the sum collapses to a single term
  rw [tsum_eq_single n]
  · -- m = n: f.val n * (1 * 1) = f.val n
    simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]
  · -- m ≠ n: f.val m * 0 = 0
    intro m hm
    simp only [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]
    by_cases ha : (Nat.unpair n).1 = (Nat.unpair m).1
    · have hb : (Nat.unpair n).2 ≠ (Nat.unpair m).2 := by
        intro hb_eq
        exact hm (by rw [← Nat.pair_unpair m, ← ha, ← hb_eq, Nat.pair_unpair])
      simp [ha, hb]
    · simp [ha]

/-- **Functoriality of `mapCLM`: composition distributes.**
`(T₁ ∘ S₁) ⊗ (T₂ ∘ S₂) = (T₁ ⊗ T₂) ∘ (S₁ ⊗ S₂)` -/
theorem nuclearTensorProduct_mapCLM_comp
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    [DyninMityaginSpace.HasBiorthogonalBasis E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    [DyninMityaginSpace.HasBiorthogonalBasis E₂]
    (T₁ S₁ : E₁ →L[ℝ] E₁) (T₂ S₂ : E₂ →L[ℝ] E₂) :
    nuclearTensorProduct_mapCLM (T₁.comp S₁) (T₂.comp S₂) =
    (nuclearTensorProduct_mapCLM T₁ T₂).comp (nuclearTensorProduct_mapCLM S₁ S₂) := by
  -- Strategy: show both CLMs agree on all basis vectors, then use DM expansion.
  ext f n
  -- Both sides applied to f, evaluated at coefficient n:
  set T_comp := nuclearTensorProduct_mapCLM (T₁.comp S₁) (T₂.comp S₂)
  set T_ST := (nuclearTensorProduct_mapCLM T₁ T₂).comp
    (nuclearTensorProduct_mapCLM S₁ S₂)
  -- Use DM expansion: φ(T f) = ∑' m, f.val m * φ(T(basisVec m))
  set φ := RapidDecaySeq.coeffCLM n
  have h_lhs : φ (T_comp f) = ∑' m, f.val m * φ (T_comp (RapidDecaySeq.basisVec m)) :=
    RapidDecaySeq.rapidDecay_expansion (φ.comp T_comp) f
  have h_rhs : φ (T_ST f) = ∑' m, f.val m * φ (T_ST (RapidDecaySeq.basisVec m)) :=
    RapidDecaySeq.rapidDecay_expansion (φ.comp T_ST) f
  -- It suffices to show they agree on each basis vector
  show φ (T_comp f) = φ (T_ST f)
  rw [h_lhs, h_rhs]
  congr 1; ext m
  congr 1
  -- Show: T_comp (basisVec m) = T_ST (basisVec m)
  -- i.e., mapCLM (T₁∘S₁) (T₂∘S₂) (basisVec m) = mapCLM T₁ T₂ (mapCLM S₁ S₂ (basisVec m))
  -- Step 1: mapCLM ... (basisVec m) unfolds to mapRapidDecay ... (basisVec m)
  -- which by biorthogonality collapses to mapImage ... m
  -- Step 2: mapImage (T₁∘S₁) (T₂∘S₂) m = mapCLM T₁ T₂ (mapImage S₁ S₂ m) by mapCLM_pure
  -- First show: mapCLM ... (basisVec m) = mapImage ... m for any CLMs
  have h_basis_comp : T_comp (RapidDecaySeq.basisVec m) =
      mapImage (T₁.comp S₁) (T₂.comp S₂) m := by
    ext k
    show (mapRapidDecay (T₁.comp S₁) (T₂.comp S₂) (RapidDecaySeq.basisVec m)).val k =
      (mapImage (T₁.comp S₁) (T₂.comp S₂) m).val k
    simp only [mapRapidDecay]
    rw [tsum_eq_single m]
    · simp [RapidDecaySeq.basisVec]
    · intro j hj
      simp [RapidDecaySeq.basisVec, hj]
  have h_basis_S : nuclearTensorProduct_mapCLM S₁ S₂ (RapidDecaySeq.basisVec m) =
      mapImage S₁ S₂ m := by
    ext k
    show (mapRapidDecay S₁ S₂ (RapidDecaySeq.basisVec m)).val k =
      (mapImage S₁ S₂ m).val k
    simp only [mapRapidDecay]
    rw [tsum_eq_single m]
    · simp [RapidDecaySeq.basisVec]
    · intro j hj
      simp [RapidDecaySeq.basisVec, hj]
  rw [h_basis_comp]
  congr 1
  -- Goal: mapImage (T₁.comp S₁) (T₂.comp S₂) m = T_ST (basisVec m)
  simp only [T_ST, ContinuousLinearMap.comp_apply, h_basis_S]
  -- Goal: mapImage (T₁∘S₁) (T₂∘S₂) m = mapCLM T₁ T₂ (mapImage S₁ S₂ m)
  simp only [mapImage, ContinuousLinearMap.comp_apply]
  exact (nuclearTensorProduct_mapCLM_pure T₁ T₂ _ _).symm

/-- **evalCLM commutes with mapCLM.**

  `evalCLM φ₁ φ₂ (mapCLM T₁ T₂ f) = evalCLM (φ₁.comp T₁) (φ₂.comp T₂) f`

On pure tensors: `φ₁(T₁ e₁) * φ₂(T₂ e₂)` = `(φ₁∘T₁)(e₁) * (φ₂∘T₂)(e₂)`.
Extension by `rapidDecay_expansion` + single-space Schauder expansion in mapImage.
TODO: prove from tsum expansion. -/
theorem evalCLM_comp_mapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (hbasis₁ : ∀ n m, DyninMityaginSpace.coeff (E := E₁) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (hbasis₂ : ∀ n m, DyninMityaginSpace.coeff (E := E₂) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ)
    (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂)
    (f : NuclearTensorProduct E₁ E₂) :
    NuclearTensorProduct.evalCLM φ₁ φ₂ (nuclearTensorProduct_mapCLM T₁ T₂ f) =
    NuclearTensorProduct.evalCLM (φ₁.comp T₁) (φ₂.comp T₂) f := by
  -- Both sides are CLMs in f that agree on basisVec.
  -- By rapidDecay_expansion, they must agree on all f.
  have key : ∀ m,
      (NuclearTensorProduct.evalCLM φ₁ φ₂).comp (nuclearTensorProduct_mapCLM T₁ T₂)
        (RapidDecaySeq.basisVec m) =
      NuclearTensorProduct.evalCLM (φ₁.comp T₁) (φ₂.comp T₂)
        (RapidDecaySeq.basisVec m) := by
    intro m
    have hbv := NuclearTensorProduct.basisVec_eq_pure hbasis₁ hbasis₂ m
    simp only [ContinuousLinearMap.comp_apply]
    rw [hbv, nuclearTensorProduct_mapCLM_pure,
        NuclearTensorProduct.evalCLM_pure,
        NuclearTensorProduct.evalCLM_pure]
    simp only [ContinuousLinearMap.comp_apply]
  -- Expand both sides via rapidDecay_expansion and apply key
  have h1 := RapidDecaySeq.rapidDecay_expansion
    ((NuclearTensorProduct.evalCLM φ₁ φ₂).comp (nuclearTensorProduct_mapCLM T₁ T₂)) f
  have h2 := RapidDecaySeq.rapidDecay_expansion
    (NuclearTensorProduct.evalCLM (φ₁.comp T₁) (φ₂.comp T₂)) f
  simp only [ContinuousLinearMap.comp_apply] at h1
  calc (NuclearTensorProduct.evalCLM φ₁ φ₂) (nuclearTensorProduct_mapCLM T₁ T₂ f)
      = ∑' m, f.val m * (NuclearTensorProduct.evalCLM φ₁ φ₂)
          (nuclearTensorProduct_mapCLM T₁ T₂ (RapidDecaySeq.basisVec m)) := h1
    _ = ∑' m, f.val m * (NuclearTensorProduct.evalCLM (φ₁.comp T₁) (φ₂.comp T₂))
          (RapidDecaySeq.basisVec m) := by
        congr 1; ext m
        simp only [ContinuousLinearMap.comp_apply] at key
        congr 1; exact key m
    _ = (NuclearTensorProduct.evalCLM (φ₁.comp T₁) (φ₂.comp T₂)) f := h2.symm

end GaussianField

end
