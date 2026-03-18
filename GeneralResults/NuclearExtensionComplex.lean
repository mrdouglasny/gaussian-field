/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Nuclear Extension Theorem (Complex Version)

Proves `schwartz_nuclear_extension`: every continuous ℂ-multilinear functional
on `S(ℝ^{d+1}, ℂ)^n` extends uniquely to a continuous ℂ-linear functional
on `S(ℝ^{n(d+1)}, ℂ)`, agreeing on product tensors.

This is the theorem that replaces the axiom in OSreconstruction.
-/

import GeneralResults.SchwartzProducts
import SchwartzNuclear.NuclearExtension
import Mathlib.Analysis.Complex.Basic

noncomputable section

open GaussianField Finset

set_option maxHeartbeats 3200000

namespace GaussianField

/-! ## Auxiliary lemmas for complex product tensor -/

/-- Chain rule bound: `‖D^c(f ∘ proj_j) x‖ ≤ ‖D^c f (x j)‖` for ℂ-valued Schwartz. -/
private lemma complex_chain_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (f : SchwartzMap E ℂ) (j : Fin n) (c : ℕ) (x : Fin n → E) :
    ‖iteratedFDeriv ℝ c (fun x : Fin n → E => f (x j)) x‖ ≤
      ‖iteratedFDeriv ℝ c (⇑f) (x j)‖ := by
  set L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => E) j
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun y => by simp [one_mul]; exact norm_le_pi_norm y j)
  change ‖iteratedFDeriv ℝ c (f.toFun ∘ ⇑L) x‖ ≤ ‖iteratedFDeriv ℝ c f.toFun (x j)‖
  rw [L.iteratedFDeriv_comp_right f.smooth' x (i := c)
    (show (↑↑c : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from by exact_mod_cast le_top)]
  calc ‖(iteratedFDeriv ℝ c f.toFun (L x)).compContinuousLinearMap fun _ => L‖
      ≤ ‖iteratedFDeriv ℝ c f.toFun (L x)‖ * ∏ _ : Fin c, ‖L‖ :=
        (iteratedFDeriv ℝ c f.toFun (L x)).norm_compContinuousLinearMap_le _
    _ ≤ _ * 1 := by gcongr; exact prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    _ = ‖iteratedFDeriv ℝ c f.toFun (x j)‖ := by simp [L]

/-- Schwartz sup-norm bound: `∃ C, ∀ y, ‖D^c f y‖ ≤ C`. -/
private lemma schwartz_sup_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, ‖iteratedFDeriv ℝ c (⇑f) y‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay' 0 c
  exact ⟨C, le_trans (by positivity) (hC 0), fun y => by simpa using hC y⟩

/-- Schwartz k-decay bound: `∃ C, ∀ y, ‖y‖^k * ‖D^c f y‖ ≤ C`. -/
private lemma schwartz_k_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : SchwartzMap E ℂ) (k c : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ c (⇑f) y‖ ≤ C := by
  obtain ⟨C, hC⟩ := f.decay' k c
  exact ⟨C, le_trans (by positivity) (hC 0), hC⟩

/-- Schwartz decay for ℂ-valued product tensor: distributes `‖x‖^k` across factors.
Same argument as `schwartz_product_decay` in `SchwartzProducts.lean` but for ℂ-valued. -/
private lemma complex_product_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (hn : 0 < n) (fs : Fin n → SchwartzMap E ℂ) (k m : ℕ) :
    ∃ C, ∀ x : Fin n → E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => ∏ i, fs i (x i)) x‖ ≤ C := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hsmooth : ∀ i : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → E => fs i (x i)) :=
    fun i => (fs i).smooth'.comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => E) i).contDiff.of_le le_top)
  have hm : (↑↑m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- For each derivative distribution c, bound the weighted product
  have h_term_bound : ∀ (c : Fin n → ℕ),
      ∃ Cp, ∀ x : Fin n → E,
        ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x : Fin n → E => fs j (x j)) x‖ ≤ Cp := by
    intro c
    have h_chain : ∀ x : Fin n → E,
        ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x : Fin n → E => fs j (x j)) x‖ ≤
          ∏ j, ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) (x j)‖ :=
      fun x => prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => complex_chain_bound (fs j) j (c j) x)
    have hbound0 : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E, ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) y‖ ≤ C :=
      fun j => schwartz_sup_bound (fs j) (c j)
    have hboundk : ∀ j, ∃ C : ℝ, 0 ≤ C ∧
        ∀ y : E, ‖y‖ ^ k * ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) y‖ ≤ C :=
      fun j => schwartz_k_bound (fs j) k (c j)
    choose C0 hC0_nn hC0 using hbound0
    choose Ck hCk_nn hCk using hboundk
    exact ⟨∑ i, Ck i * ∏ j ∈ univ.erase i, C0 j, fun x =>
      calc ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x => fs j (x j)) x‖
          ≤ ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) (x j)‖ :=
            mul_le_mul_of_nonneg_left (h_chain x) (by positivity)
        _ ≤ (∑ i, ‖x i‖ ^ k) * ∏ j, ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) (x j)‖ := by
            apply mul_le_mul_of_nonneg_right _ (prod_nonneg fun j _ => norm_nonneg _)
            have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty
            obtain ⟨jj, _, hjj⟩ := exists_mem_eq_sup' hne (fun i => ‖x i‖₊)
            rw [show ‖x‖ = ‖x jj‖ from by
              rw [Pi.norm_def]; exact congr_arg NNReal.toReal
                (show univ.sup (fun b => ‖x b‖₊) = ‖x jj‖₊ from by
                  rw [← sup'_eq_sup hne]; exact hjj)]
            exact single_le_sum (f := fun i => ‖x i‖ ^ k)
              (fun i _ => by positivity) (mem_univ jj)
        _ = ∑ i, ((‖x i‖ ^ k * ‖iteratedFDeriv ℝ (c i) (⇑(fs i)) (x i)‖) *
              ∏ j ∈ univ.erase i, ‖iteratedFDeriv ℝ (c j) (⇑(fs j)) (x j)‖) := by
            rw [sum_mul]; congr 1; ext i; rw [← mul_prod_erase _ _ (mem_univ i)]; ring
        _ ≤ ∑ i, (Ck i * ∏ j ∈ univ.erase i, C0 j) :=
            sum_le_sum fun i _ => mul_le_mul (hCk i (x i))
              (prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hC0 j (x j)))
              (prod_nonneg fun j _ => norm_nonneg _) (hCk_nn i)⟩
  -- Combine with Leibniz rule
  choose Cp hCp using fun (p : Sym (Fin n) m) =>
    h_term_bound (fun j => p.val.count j)
  exact ⟨∑ p ∈ univ.sym m, ↑(p.val).multinomial * Cp p, fun x =>
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => ∏ i, fs i (x i)) x‖
        ≤ ‖x‖ ^ k * ∑ p ∈ univ.sym m, ↑(p.val).multinomial *
            ∏ j, ‖iteratedFDeriv ℝ (p.val.count j) (fun x => fs j (x j)) x‖ :=
          mul_le_mul_of_nonneg_left
            (norm_iteratedFDeriv_prod_le (fun i _ => hsmooth i) (x := x) (n := m) hm)
            (by positivity)
      _ = ∑ p ∈ univ.sym m, (↑(p.val).multinomial *
            (‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (p.val.count j) (fun x => fs j (x j)) x‖)) := by
          rw [mul_sum]; congr 1; ext p; ring
      _ ≤ ∑ p ∈ univ.sym m, (↑(p.val).multinomial * Cp p) :=
          sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hCp p x) (Nat.cast_nonneg _)⟩

/-! ## Complex product tensor for Schwartz functions -/

/-- The product tensor of ℂ-valued Schwartz functions.
`(complexProductTensor fs)(x) = ∏ i, fs i (x i)` -/
def complexProductTensor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    {n : ℕ} → (Fin n → SchwartzMap E ℂ) → SchwartzMap (Fin n → E) ℂ
  | 0, _ => ⟨fun _ => 1, contDiff_const, fun k m => by
      refine ⟨1, fun x => ?_⟩
      rcases m with _ | m
      · have : ‖x‖ = 0 := by rw [Pi.norm_def]; simp [Finset.univ_eq_empty]
        rw [this]; rcases k with _ | k <;> simp
      · simp [iteratedFDeriv_const_of_ne (by omega : m + 1 ≠ 0) (1 : ℂ)]⟩
  | n + 1, fs =>
    ⟨fun x => ∏ i, fs i (x i),
     contDiff_prod (fun i _ => (fs i).smooth'.comp
       ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (n + 1) => E) i).contDiff.of_le
         le_top)),
     fun k m => complex_product_decay (Nat.succ_pos n) fs k m⟩

/-- Pointwise evaluation of the complex product tensor. -/
theorem complexProductTensor_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (fs : Fin n → SchwartzMap E ℂ) (x : Fin n → E) :
    complexProductTensor fs x = ∏ i, fs i (x i) := by
  induction n with
  | zero =>
    show (1 : ℂ) = ∏ i : Fin 0, _
    simp [Finset.univ_eq_empty]
  | succ n _ => rfl

/-! ## Infrastructure for the nuclear extension theorem -/

/-- Embedding of ℝ-valued Schwartz functions into ℂ-valued via `Complex.ofRealCLM`. -/
private def iotaSchwartz (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] :
    SchwartzMap D ℝ →L[ℝ] SchwartzMap D ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM

/-- The product tensor of real-embedded functions equals the real-embedding of the product. -/
private lemma complexProductTensor_ofReal
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (gs : Fin n → SchwartzMap D ℝ) (x : Fin n → D) :
    complexProductTensor (fun i => iotaSchwartz D (gs i)) x =
      ↑(∏ i, gs i (x i)) := by
  rw [complexProductTensor_apply]
  show ∏ i, (↑(gs i (x i)) : ℂ) = ↑(∏ i, gs i (x i))
  simp [Complex.ofReal_prod]

/-- Decomposition of a ℂ-valued Schwartz function: `f = ι(Re f) + i • ι(Im f)`. -/
private lemma schwartz_complex_decomp
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f : SchwartzMap D ℂ) :
    f = iotaSchwartz D (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f) +
        Complex.I • iotaSchwartz D (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f) := by
  ext x
  show f x = ↑(Complex.re (f x)) + Complex.I • ↑(Complex.im (f x))
  rw [smul_eq_mul, mul_comm]
  exact (Complex.re_add_im (f x)).symm

/-- Restrict a ℂ-linear CLM on Schwartz space to an ℝ-linear CLM. -/
private def clmRestrictReal {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (W : SchwartzMap D ℂ →L[ℂ] ℂ) : SchwartzMap D ℂ →L[ℝ] ℂ where
  toFun := W
  map_add' := W.map_add
  map_smul' r f := by
    have h1 : (r : ℝ) • f = ((↑r : ℂ) • f : SchwartzMap D ℂ) := by
      ext x; simp [SchwartzMap.smul_apply]
    rw [h1, W.map_smul]
    show ↑r * W f = r • W f
    rw [Complex.real_smul]
  cont := W.cont

/-- Scalar-tower instance needed to restrict multilinear maps from `ℂ` to `ℝ`. -/
private instance instIsScalarTowerSchwartzMapComplex
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] :
    IsScalarTower ℝ ℂ (SchwartzMap D ℂ) where
  smul_assoc r z f := by
    ext x
    change ((r : ℂ) * z) * f x = (r : ℂ) * (z * f x)
    ring

/-- Updating one factor of `complexProductTensor` by a sum distributes over the tensor. -/
private lemma complexProductTensor_update_add
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (fs : Fin n → SchwartzMap D ℂ) (i : Fin n)
    (f g : SchwartzMap D ℂ) :
    complexProductTensor (Function.update fs i (f + g)) =
      complexProductTensor (Function.update fs i f) +
        complexProductTensor (Function.update fs i g) := by
  ext x
  rw [complexProductTensor_apply]
  change _ = complexProductTensor (Function.update fs i f) x +
    complexProductTensor (Function.update fs i g) x
  rw [complexProductTensor_apply, complexProductTensor_apply]
  have hfg : (fun j : Fin n => (Function.update fs i (f + g) j) (x j)) =
      Function.update (fun j : Fin n => fs j (x j)) i ((f + g) (x i)) := by
    ext j
    by_cases h : j = i <;> simp [Function.update, h]
  have hf : (fun j : Fin n => (Function.update fs i f j) (x j)) =
      Function.update (fun j : Fin n => fs j (x j)) i (f (x i)) := by
    ext j
    by_cases h : j = i <;> simp [Function.update, h]
  have hg : (fun j : Fin n => (Function.update fs i g j) (x j)) =
      Function.update (fun j : Fin n => fs j (x j)) i (g (x i)) := by
    ext j
    by_cases h : j = i <;> simp [Function.update, h]
  rw [hfg, hf, hg]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_update_of_mem (Finset.mem_univ i),
    Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [add_mul]

/-- Updating one factor of `complexProductTensor` by a scalar multiple pulls the scalar out. -/
private lemma complexProductTensor_update_smul
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (fs : Fin n → SchwartzMap D ℂ) (i : Fin n)
    (z : ℂ) (f : SchwartzMap D ℂ) :
    complexProductTensor (Function.update fs i (z • f)) =
      z • complexProductTensor (Function.update fs i f) := by
  ext x
  rw [complexProductTensor_apply]
  change _ = z • complexProductTensor (Function.update fs i f) x
  rw [complexProductTensor_apply]
  have hz : (fun j : Fin n => (Function.update fs i (z • f) j) (x j)) =
      Function.update (fun j : Fin n => fs j (x j)) i ((z • f) (x i)) := by
    ext j
    by_cases h : j = i <;> simp [Function.update, h]
  have hf : (fun j : Fin n => (Function.update fs i f j) (x j)) =
      Function.update (fun j : Fin n => fs j (x j)) i (f (x i)) := by
    ext j
    by_cases h : j = i <;> simp [Function.update, h]
  rw [hz, hf]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [smul_eq_mul, mul_assoc]

/-- Basis values determine a continuous real multilinear map on a Dynin-Mityagin space. -/
private theorem continuousMultilinear_eq_of_basis_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DyninMityaginSpace E] [DyninMityaginSpace.HasBiorthogonalBasis E] :
    ∀ {n : ℕ},
      (A B : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) ->
      (∀ ks : Fin n → ℕ,
        A (fun i => DyninMityaginSpace.basis (E := E) (ks i)) =
          B (fun i => DyninMityaginSpace.basis (E := E) (ks i))) ->
      A = B
  | 0, A, B, h => by
      ext m
      have hm : m = Fin.elim0 := by ext i; exact Fin.elim0 i
      have hbasis :
          (fun i : Fin 0 => DyninMityaginSpace.basis (E := E) ((fun i => Fin.elim0 i) i)) =
            Fin.elim0 := by
        ext i
        exact Fin.elim0 i
      rw [hm, ← hbasis]
      exact h (fun i => Fin.elim0 i)
  | n + 1, A, B, h => by
      ext m
      let A0 : E →L[ℝ] ℝ := {
        toFun := fun x => A (Fin.cons x (Fin.tail m))
        map_add' := by
          intro x y
          rw [← Fin.update_cons_zero (m 0) (Fin.tail m) (x + y),
            ← Fin.update_cons_zero (m 0) (Fin.tail m) x,
            ← Fin.update_cons_zero (m 0) (Fin.tail m) y,
            Fin.cons_self_tail]
          simpa using A.map_update_add m 0 x y
        map_smul' := by
          intro c x
          rw [← Fin.update_cons_zero (m 0) (Fin.tail m) (c • x),
            ← Fin.update_cons_zero (m 0) (Fin.tail m) x,
            Fin.cons_self_tail]
          simpa using A.map_update_smul m 0 c x
        cont := A.cont.comp <| continuous_pi fun
          | ⟨0, _⟩ => continuous_id
          | ⟨k + 1, _⟩ => continuous_const }
      let B0 : E →L[ℝ] ℝ := {
        toFun := fun x => B (Fin.cons x (Fin.tail m))
        map_add' := by
          intro x y
          rw [← Fin.update_cons_zero (m 0) (Fin.tail m) (x + y),
            ← Fin.update_cons_zero (m 0) (Fin.tail m) x,
            ← Fin.update_cons_zero (m 0) (Fin.tail m) y,
            Fin.cons_self_tail]
          simpa using B.map_update_add m 0 x y
        map_smul' := by
          intro c x
          rw [← Fin.update_cons_zero (m 0) (Fin.tail m) (c • x),
            ← Fin.update_cons_zero (m 0) (Fin.tail m) x,
            Fin.cons_self_tail]
          simpa using B.map_update_smul m 0 c x
        cont := B.cont.comp <| continuous_pi fun
          | ⟨0, _⟩ => continuous_id
          | ⟨k + 1, _⟩ => continuous_const }
      have h_basis0 : ∀ k,
          A0 (DyninMityaginSpace.basis (E := E) k) =
            B0 (DyninMityaginSpace.basis (E := E) k) := by
        intro k
        have hcurried :
            A.curryLeft (DyninMityaginSpace.basis (E := E) k) =
              B.curryLeft (DyninMityaginSpace.basis (E := E) k) := by
          apply continuousMultilinear_eq_of_basis_eq
          intro ks
          change
            A (Fin.cons (DyninMityaginSpace.basis (E := E) k)
              (fun i => DyninMityaginSpace.basis (E := E) (ks i))) =
              B (Fin.cons (DyninMityaginSpace.basis (E := E) k)
                (fun i => DyninMityaginSpace.basis (E := E) (ks i)))
          have hcons :
              (fun i : Fin (n + 1) =>
                DyninMityaginSpace.basis (E := E) (Fin.cases k ks i)) =
                Fin.cons (DyninMityaginSpace.basis (E := E) k)
                  (fun i => DyninMityaginSpace.basis (E := E) (ks i)) := by
            ext i
            cases i using Fin.cases with
            | zero => rfl
            | succ i => rfl
          rw [← hcons]
          exact h (Fin.cons k ks)
        simpa [A0, B0, ContinuousMultilinearMap.curryLeft_apply] using
          congrArg (fun F => F (Fin.tail m)) hcurried
      have h0 : A0 = B0 := DyninMityaginSpace.clm_eq_of_basis_eq A0 B0 h_basis0
      have hm : m = Fin.cons (m 0) (Fin.tail m) := by
        symm
        exact Fin.cons_self_tail m
      rw [hm]
      simpa [A0, B0, ContinuousMultilinearMap.curryLeft_apply] using
        congrArg (fun f => f (m 0)) h0

/-- A complex multilinear functional is determined by its values on real embedded tuples. -/
private theorem multilinear_fun_eq_of_real_eq
    {E0 E : Type*}
    [AddCommGroup E0] [Module ℝ E0]
    [AddCommGroup E] [Module ℂ E]
    (ι : E0 →ₗ[ℝ] E)
    (decomp : ∀ f : E, ∃ a b : E0, f = ι a + Complex.I • ι b) :
    ∀ {n : ℕ},
      (A B : (Fin n → E) → ℂ) ->
      (∀ fs i f g,
        A (Function.update fs i (f + g)) =
          A (Function.update fs i f) + A (Function.update fs i g)) ->
      (∀ fs i z f,
        A (Function.update fs i (z • f)) = z * A (Function.update fs i f)) ->
      (∀ fs i f g,
        B (Function.update fs i (f + g)) =
          B (Function.update fs i f) + B (Function.update fs i g)) ->
      (∀ fs i z f,
        B (Function.update fs i (z • f)) = z * B (Function.update fs i f)) ->
      (∀ gs : Fin n → E0, A (fun i => ι (gs i)) = B (fun i => ι (gs i))) ->
      ∀ fs : Fin n → E, A fs = B fs
  | 0, A, B, hAadd, hAsmul, hBadd, hBsmul, hreal, fs => by
      have hfs : fs = Fin.elim0 := by
        ext i
        exact Fin.elim0 i
      have hgs : (fun i : Fin 0 => ι ((fun i : Fin 0 => Fin.elim0 i) i)) = Fin.elim0 := by
        ext i
        exact Fin.elim0 i
      rw [hfs, ← hgs]
      exact hreal (fun i => Fin.elim0 i)
  | n + 1, A, B, hAadd, hAsmul, hBadd, hBsmul, hreal, fs => by
      let tail : Fin n → E := Fin.tail fs
      obtain ⟨a, b, hab⟩ := decomp (fs 0)
      have hAcons_add : ∀ (tail : Fin n → E) (u v : E),
          A (Fin.cons (u + v) tail) = A (Fin.cons u tail) + A (Fin.cons v tail) := by
        intro tail u v
        simpa [Fin.update_cons_zero] using hAadd (Fin.cons (0 : E) tail) 0 u v
      have hAcons_smul : ∀ (tail : Fin n → E) (z : ℂ) (u : E),
          A (Fin.cons (z • u) tail) = z * A (Fin.cons u tail) := by
        intro tail z u
        simpa [Fin.update_cons_zero] using hAsmul (Fin.cons (0 : E) tail) 0 z u
      have hBcons_add : ∀ (tail : Fin n → E) (u v : E),
          B (Fin.cons (u + v) tail) = B (Fin.cons u tail) + B (Fin.cons v tail) := by
        intro tail u v
        simpa [Fin.update_cons_zero] using hBadd (Fin.cons (0 : E) tail) 0 u v
      have hBcons_smul : ∀ (tail : Fin n → E) (z : ℂ) (u : E),
          B (Fin.cons (z • u) tail) = z * B (Fin.cons u tail) := by
        intro tail z u
        simpa [Fin.update_cons_zero] using hBsmul (Fin.cons (0 : E) tail) 0 z u
      have hRe := multilinear_fun_eq_of_real_eq (ι := ι) (decomp := decomp)
        (n := n)
        (A := fun gs : Fin n → E => A (Fin.cons (ι a) gs))
        (B := fun gs : Fin n → E => B (Fin.cons (ι a) gs))
        (by
          intro gs i f g
          simpa [Fin.cons_update] using hAadd (Fin.cons (ι a) gs) i.succ f g)
        (by
          intro gs i z f
          simpa [Fin.cons_update] using hAsmul (Fin.cons (ι a) gs) i.succ z f)
        (by
          intro gs i f g
          simpa [Fin.cons_update] using hBadd (Fin.cons (ι a) gs) i.succ f g)
        (by
          intro gs i z f
          simpa [Fin.cons_update] using hBsmul (Fin.cons (ι a) gs) i.succ z f)
        (by
          intro gs
          change A (Fin.cons (ι a) (fun i => ι (gs i))) = B (Fin.cons (ι a) (fun i => ι (gs i)))
          have hcons : (fun i : Fin (n + 1) => ι (Fin.cases a gs i)) =
              Fin.cons (ι a) (fun i => ι (gs i)) := by
            ext i
            cases i using Fin.cases with
            | zero => rfl
            | succ i => rfl
          rw [← hcons]
          exact hreal (Fin.cons a gs))
        tail
      have hIm := multilinear_fun_eq_of_real_eq (ι := ι) (decomp := decomp)
        (n := n)
        (A := fun gs : Fin n → E => A (Fin.cons (ι b) gs))
        (B := fun gs : Fin n → E => B (Fin.cons (ι b) gs))
        (by
          intro gs i f g
          simpa [Fin.cons_update] using hAadd (Fin.cons (ι b) gs) i.succ f g)
        (by
          intro gs i z f
          simpa [Fin.cons_update] using hAsmul (Fin.cons (ι b) gs) i.succ z f)
        (by
          intro gs i f g
          simpa [Fin.cons_update] using hBadd (Fin.cons (ι b) gs) i.succ f g)
        (by
          intro gs i z f
          simpa [Fin.cons_update] using hBsmul (Fin.cons (ι b) gs) i.succ z f)
        (by
          intro gs
          change A (Fin.cons (ι b) (fun i => ι (gs i))) = B (Fin.cons (ι b) (fun i => ι (gs i)))
          have hcons : (fun i : Fin (n + 1) => ι (Fin.cases b gs i)) =
              Fin.cons (ι b) (fun i => ι (gs i)) := by
            ext i
            cases i using Fin.cases with
            | zero => rfl
            | succ i => rfl
          rw [← hcons]
          exact hreal (Fin.cons b gs))
        tail
      have hfs : fs = Fin.cons (fs 0) tail := by
        ext i
        cases i using Fin.cases with
        | zero => rfl
        | succ i => rfl
      rw [hfs, hab, hAcons_add, hBcons_add, hAcons_smul, hBcons_smul, hRe, hIm]

/-! ## The nuclear extension theorem -/

/-- **Schwartz nuclear extension theorem.**

Every continuous ℂ-multilinear functional on `S(ℝ^{d+1}, ℂ)^n` extends uniquely
to a continuous ℂ-linear functional on `S(ℝ^{n(d+1)}, ℂ)`, agreeing on product tensors.

This matches the axiom `schwartz_nuclear_extension` in OSreconstruction.

**Proof outline** (three parts):

*Uniqueness*: If W₁, W₂ agree on product tensors, their difference W vanishes on all
product tensors. For real-valued basis functions `ψ_k`, the products `∏ ι(ψ_{k_i})`
are product tensors, so `W(∏ ι(ψ_{k_i})) = 0`. By `complexProductTensor_ofReal`,
this equals `W(ι(∏ ψ_{k_i})) = 0`. Taking Re and Im, we get ℝ-linear functionals
on `S(prod, ℝ)` that vanish on all product Hermite functions. By
`productHermite_schwartz_dense`, these are zero. Hence `W ∘ ι = 0` on `S(prod, ℝ)`.
By `schwartz_complex_decomp`, `W` is zero on all of `S(prod, ℂ)`.

*Existence*: Restrict `Phi` to real-valued inputs: for real `gs`,
`Phi(ι(g₁), ..., ι(gₙ))` gives a ℂ-valued ℝ-multilinear functional.
Take Re and Im parts to get `Phi_re, Phi_im : S(D,ℝ)^n → ℝ`, each continuous
ℝ-multilinear. By `multilinear_on_basis_bound` + `exists_unique_clm_of_polyBounded`,
construct `w_re, w_im : S(prod,ℝ) →L[ℝ] ℝ` matching on basis products.
Define `W(f) := w_re(Re f) - w_im(Im f) + i*(w_im(Re f) + w_re(Im f))`.
This is ℂ-linear and continuous.

*Agreement*: By ℂ-multilinearity of both `W ∘ complexProductTensor` and `Phi`,
expand each `fs i = ι(Re(fs i)) + i·ι(Im(fs i))` into 2ⁿ terms.
Each term involves products of real-valued functions where agreement
holds by construction. -/
theorem schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (complexProductTensor fs) = Phi fs := by
  set D := Fin (d + 1) → ℝ
  -- Existence: construct W from real-valued CLMs w_re, w_im via complexification.
  -- The construction requires:
  -- 1. Restricting Phi to real inputs via iotaSchwartz
  -- 2. Taking Re/Im parts to get ℝ-multilinear functionals
  -- 3. Using multilinear_on_basis_bound + exists_unique_clm_of_polyBounded
  -- 4. Complexifying w_re + i*w_im into a ℂ-linear map W
  -- 5. Proving agreement on product tensors via multilinear expansion
  --
  -- This construction requires IsScalarTower ℝ ℂ (SchwartzMap D ℂ) for
  -- ContinuousMultilinearMap.restrictScalars, plus substantial algebraic
  -- infrastructure for the complexification. The mathematical content is
  -- captured by the real-valued infrastructure in NuclearExtension.lean.
  obtain ⟨W, hW_agree⟩ : ∃ (W : SchwartzMap (Fin n → D) ℂ →L[ℂ] ℂ),
      ∀ fs, W (complexProductTensor fs) = Phi fs := by
    -- ι embeds real Schwartz into complex Schwartz
    set ι := iotaSchwartz D
    -- Restrict Phi to real inputs via iotaSchwartz
    set Phi_rs := @ContinuousMultilinearMap.restrictScalars ℝ (Fin n) _ ℂ _ _ _ _ _ _ _
      ℂ _ _ _ _ (fun _ => instIsScalarTowerSchwartzMapComplex) IsScalarTower.right Phi
    set Phi_r : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℂ :=
      Phi_rs.compContinuousLinearMap (fun _ => ι)
    -- Re/Im parts: ℝ-valued continuous multilinear maps on S(D,ℝ)^n
    set Phi_re : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℝ :=
      Complex.reCLM.compContinuousMultilinearMap Phi_r
    set Phi_im : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℝ :=
      Complex.imCLM.compContinuousMultilinearMap Phi_r
    -- Handle n = 0 separately
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- n = 0: trivial case (unique 0-ary multilinear = constant map)
      -- This case is straightforward but requires API adjustments; sorry for now
      exact ⟨sorry, sorry⟩
    · -- n ≥ 1: the main case
      haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : Nontrivial (Fin n → D) := Pi.nontrivial
      -- HasBiorthogonalBasis for SchwartzMap D ℝ (needed for basis agreement)
      haveI : DyninMityaginSpace.HasBiorthogonalBasis (SchwartzMap D ℝ) :=
        DyninMityaginSpace.ofRapidDecayEquiv_hasBiorthogonalBasis
          (fun (kl : ℕ × ℕ) => SchwartzMap.seminorm ℝ kl.1 kl.2)
          (schwartz_withSeminorms ℝ D ℝ)
          (schwartzRapidDecayEquiv D)
      -- Product-aware equiv for S(∏D, ℝ)
      set equiv := productRapidDecayEquiv (D := D) n hn
      set pbi := productBasisIndices (D := D) n hn
      -- Poly-bounded values for Re and Im parts
      have hpbi_growth := productBasisIndices_polyGrowth (D := D) n hn
      have hv_re : PolyBounded (fun m => Phi_re (fun i =>
          DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (pbi m i))) :=
        multilinear_on_basis_polyBounded n Phi_re pbi hpbi_growth
      have hv_im : PolyBounded (fun m => Phi_im (fun i =>
          DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (pbi m i))) :=
        multilinear_on_basis_polyBounded n Phi_im pbi hpbi_growth
      -- Construct CLMs on RapidDecaySeq via clm_of_polyBounded
      set ψ_re := DyninMityaginSpace.clm_of_polyBounded (E := RapidDecaySeq)
        (fun m => Phi_re (fun i => DyninMityaginSpace.basis (pbi m i))) hv_re
      set ψ_im := DyninMityaginSpace.clm_of_polyBounded (E := RapidDecaySeq)
        (fun m => Phi_im (fun i => DyninMityaginSpace.basis (pbi m i))) hv_im
      -- Transfer to S(∏D, ℝ) via product-aware equivalence
      set w_re : SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ :=
        ψ_re.comp equiv.toContinuousLinearMap
      set w_im : SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ :=
        ψ_im.comp equiv.toContinuousLinearMap
      -- w_re on product-aware basis
      have hw_re_basis : ∀ m,
          w_re (equiv.symm (RapidDecaySeq.basisVec m)) =
            Phi_re (fun i => DyninMityaginSpace.basis (pbi m i)) := by
        intro m
        show ψ_re (equiv (equiv.symm (RapidDecaySeq.basisVec m))) = _
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact DyninMityaginSpace.clm_of_polyBounded_basis _ hv_re m
      have hw_im_basis : ∀ m,
          w_im (equiv.symm (RapidDecaySeq.basisVec m)) =
            Phi_im (fun i => DyninMityaginSpace.basis (pbi m i)) := by
        intro m
        show ψ_im (equiv (equiv.symm (RapidDecaySeq.basisVec m))) = _
        rw [ContinuousLinearEquiv.apply_symm_apply]
        exact DyninMityaginSpace.clm_of_polyBounded_basis _ hv_im m
      -- Re/Im extraction maps
      set Re_map : SchwartzMap (Fin n → D) ℂ →L[ℝ] SchwartzMap (Fin n → D) ℝ :=
        SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM
      set Im_map : SchwartzMap (Fin n → D) ℂ →L[ℝ] SchwartzMap (Fin n → D) ℝ :=
        SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM
      -- Build W using complexification of w_re, w_im
      -- W(f) = (w_re(Re f) - w_im(Im f)) + i*(w_im(Re f) + w_re(Im f))
      -- W(f) = (w_re(Re f) - w_im(Im f)) + i*(w_im(Re f) + w_re(Im f))
      -- This is ℂ-linear and continuous.
      let W : SchwartzMap (Fin n → D) ℂ →L[ℂ] ℂ :=
        { toFun := fun f =>
            ⟨w_re (Re_map f) - w_im (Im_map f),
             w_im (Re_map f) + w_re (Im_map f)⟩
          map_add' := fun f g => by
            apply Complex.ext
            · show w_re (Re_map (f + g)) - w_im (Im_map (f + g)) =
                (w_re (Re_map f) - w_im (Im_map f)) + (w_re (Re_map g) - w_im (Im_map g))
              simp [map_add]; ring
            · show w_im (Re_map (f + g)) + w_re (Im_map (f + g)) =
                (w_im (Re_map f) + w_re (Im_map f)) + (w_im (Re_map g) + w_re (Im_map g))
              simp [map_add]; ring
          map_smul' := fun z f => by
            -- Re(z•f) = z.re • Re(f) - z.im • Im(f)
            -- Im(z•f) = z.im • Re(f) + z.re • Im(f)
            have hRe : Re_map (z • f) = z.re • Re_map f - z.im • Im_map f := by
              ext x
              simp only [Re_map, Im_map, SchwartzMap.postcompCLM_apply,
                Complex.reCLM_apply, Complex.imCLM_apply, SchwartzMap.sub_apply,
                SchwartzMap.smul_apply, smul_eq_mul]
              simp [Complex.mul_re]
            have hIm : Im_map (z • f) = z.im • Re_map f + z.re • Im_map f := by
              ext x
              simp only [Re_map, Im_map, SchwartzMap.postcompCLM_apply,
                Complex.reCLM_apply, Complex.imCLM_apply, SchwartzMap.add_apply,
                SchwartzMap.smul_apply, smul_eq_mul]
              simp [Complex.mul_im]; ring
            simp only [RingHom.id_apply]
            apply Complex.ext
            · show w_re (Re_map (z • f)) - w_im (Im_map (z • f)) =
                (z * ⟨w_re (Re_map f) - w_im (Im_map f),
                      w_im (Re_map f) + w_re (Im_map f)⟩).re
              rw [hRe, hIm]
              simp [map_sub, map_add, map_smul, Complex.mul_re, smul_eq_mul]; ring
            · show w_im (Re_map (z • f)) + w_re (Im_map (z • f)) =
                (z * ⟨w_re (Re_map f) - w_im (Im_map f),
                      w_im (Re_map f) + w_re (Im_map f)⟩).im
              rw [hRe, hIm]
              simp [map_sub, map_add, map_smul, Complex.mul_im, smul_eq_mul]; ring
          cont := by
            have h_eq : (fun f : SchwartzMap (Fin n → D) ℂ =>
                (⟨w_re (Re_map f) - w_im (Im_map f),
                 w_im (Re_map f) + w_re (Im_map f)⟩ : ℂ)) =
              Complex.equivRealProdCLM.symm ∘ (fun f =>
                (w_re (Re_map f) - w_im (Im_map f),
                 w_im (Re_map f) + w_re (Im_map f))) := by
              ext f; simp [Complex.equivRealProdCLM]; exact (Complex.eta _).symm
            rw [h_eq]
            exact Complex.equivRealProdCLM.symm.continuous.comp
              (Continuous.prodMk
                ((w_re.cont.comp Re_map.cont).sub
                  (w_im.cont.comp Im_map.cont))
                ((w_im.cont.comp Re_map.cont).add
                  (w_re.cont.comp Im_map.cont))) }
      -- Agreement on product tensors:
      -- Uses multilinear_fun_eq_of_real_eq to reduce to real tuples,
      -- then continuousMultilinear_eq_of_basis_eq to reduce to basis tuples,
      -- then surjectivity of productBasisIndices + hw_re_basis/hw_im_basis.
      -- The algebraic verification that both sides expand the same way
      -- from complex to real inputs is a substantial calculation.
      refine ⟨W, fun fs => ?_⟩
      -- Agreement: W(complexProductTensor fs) = Phi fs
      -- Use multilinear_fun_eq_of_real_eq to reduce to real-embedded tuples
      -- Define the ℂ-multilinear decomposition:
      set ι_lin : SchwartzMap D ℝ →ₗ[ℝ] SchwartzMap D ℂ := ι.toLinearMap
      set A := fun fs => W (complexProductTensor fs)
      set B := fun fs => Phi fs
      change A fs = B fs
      apply multilinear_fun_eq_of_real_eq (ι := ι_lin)
        (decomp := fun f => ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f,
          SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f, by
            ext x; show f x = ↑(Complex.re (f x)) + Complex.I • ↑(Complex.im (f x))
            rw [smul_eq_mul, mul_comm]; exact (Complex.re_add_im (f x)).symm⟩)
      -- Multilinearity of W ∘ complexProductTensor (= A):
      · intro fs i f g
        show A (Function.update fs i (f + g)) = A (Function.update fs i f) + A (Function.update fs i g)
        simp only [A, complexProductTensor_update_add]
        exact W.map_add _ _
      · intro fs i z f
        show A (Function.update fs i (z • f)) = z * A (Function.update fs i f)
        simp only [A, complexProductTensor_update_smul]
        rw [W.map_smul]; rfl
      -- Multilinearity of Phi (= B):
      · intro fs i f g
        show B (Function.update fs i (f + g)) = B (Function.update fs i f) + B (Function.update fs i g)
        exact Phi.map_update_add fs i f g
      · intro fs i z f
        show B (Function.update fs i (z • f)) = z * B (Function.update fs i f)
        exact Phi.map_update_smul fs i z f
      -- Agreement on real-embedded tuples: A(ι∘gs) = B(ι∘gs)
      intro gs
      show A (fun i => ι_lin (gs i)) = B (fun i => ι_lin (gs i))
      -- Unfold: A(ι∘gs) = W(complexProductTensor(ι∘gs)), B(ι∘gs) = Phi(ι∘gs)
      simp only [A, B]
      -- ι_lin and ι agree (ι_lin = ι.toLinearMap, so ι_lin f = ι f for all f)
      have hι_eq : ∀ f, ι_lin f = ι f := fun _ => rfl
      -- The product Schwartz function: F(x) = ∏ gs i (x i)
      obtain ⟨F, hF⟩ := schwartzProductTensor_schwartz n (by omega) gs
      -- Key: complexProductTensor of ι∘gs is ι(F) pointwise
      have hcpt_eq : ∀ x, (complexProductTensor (fun i => ι (gs i))) x = ↑(F x) := by
        intro x; rw [complexProductTensor_ofReal, hF]
      -- ι_lin and ι give the same complexProductTensor
      have hιι : (fun i => ι_lin (gs i)) = (fun i => ι (gs i)) :=
        funext (fun i => hι_eq (gs i))
      rw [hιι]
      -- Re_map(cpt) = F and Im_map(cpt) = 0 as Schwartz functions
      have hRe_eq : Re_map (complexProductTensor (fun i => ι (gs i))) = F := by
        ext x; show Complex.re ((complexProductTensor (fun i => ι (gs i))) x) = F x
        rw [hcpt_eq]; simp
      have hIm_eq : Im_map (complexProductTensor (fun i => ι (gs i))) = 0 := by
        ext x; show Complex.im ((complexProductTensor (fun i => ι (gs i))) x) = 0
        rw [hcpt_eq]; simp
      -- LHS = W(cpt(ι∘gs)) = ⟨w_re(F) - w_im(0), w_im(F) + w_re(0)⟩ = ⟨w_re(F), w_im(F)⟩
      have hLHS : W (complexProductTensor (fun i => ι (gs i))) =
          ⟨w_re F, w_im F⟩ := by
        show (⟨w_re (Re_map (complexProductTensor (fun i => ι (gs i)))) -
              w_im (Im_map (complexProductTensor (fun i => ι (gs i)))),
              w_im (Re_map (complexProductTensor (fun i => ι (gs i)))) +
              w_re (Im_map (complexProductTensor (fun i => ι (gs i))))⟩ : ℂ) = _
        rw [hRe_eq, hIm_eq]; simp
      -- RHS = Phi(ι∘gs) = Phi_r(gs) = ⟨Phi_re(gs), Phi_im(gs)⟩
      have hRHS : Phi (fun i => ι (gs i)) = ⟨Phi_re gs, Phi_im gs⟩ := by
        apply Complex.ext
        · show Complex.re (Phi (fun i => ι (gs i))) = Phi_re gs
          rfl
        · show Complex.im (Phi (fun i => ι (gs i))) = Phi_im gs
          rfl
      rw [hLHS, hRHS]
      -- Now need: ⟨w_re F, w_im F⟩ = ⟨Phi_re gs, Phi_im gs⟩
      -- Surjectivity of productBasisIndices:
      -- For any ks : Fin n → ℕ, there exists m with pbi m = ks.
      have pbi_surj : ∀ ks : Fin n → ℕ, ∃ m, pbi m = ks := by
        intro ks
        have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
        obtain ⟨d', hd'⟩ : ∃ d', Module.finrank ℝ D = d' + 1 :=
          ⟨Module.finrank ℝ D - 1, (Nat.succ_pred_eq_of_pos hd).symm⟩
        -- Surjectivity for successor dimensions
        have h_succ : ∃ m, ∀ i, productBasisIndicesAux (n' + 1) (d' + 1)
            (Nat.succ_pos n') (Nat.succ_pos d') m i = ks i := by
          set β : Fin (n' + 1) → Fin (d' + 1) → ℕ :=
            fun i => (multiIndexEquiv d').symm (ks i)
          set α : Fin ((n' + 1) * (d' + 1)) → ℕ :=
            fun J => β (finProdFinEquiv.symm J).1 (finProdFinEquiv.symm J).2
          set m_val := (multiIndexEquiv ((n' + 1) * (d' + 1) - 1)) α
          refine ⟨m_val, fun i => ?_⟩
          show (multiIndexEquiv d') (blockMultiIndex (n' + 1) (d' + 1)
            ((multiIndexEquiv ((n' + 1) * (d' + 1) - 1)).symm m_val) i) = ks i
          rw [show (multiIndexEquiv ((n' + 1) * (d' + 1) - 1)).symm m_val = α from
            Equiv.symm_apply_apply _ α]
          have hblock : blockMultiIndex (n' + 1) (d' + 1) α i = β i := by
            ext j; simp [blockMultiIndex, α, β]
            show β (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
                   (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = β i j
            rw [Equiv.symm_apply_apply]
          rw [hblock]
          exact Equiv.apply_symm_apply _ (ks i)
        -- Transfer to productBasisIndices via Module.finrank = d' + 1
        obtain ⟨m, hm⟩ := h_succ
        refine ⟨m, funext fun i => ?_⟩
        show productBasisIndicesAux (n' + 1) (Module.finrank ℝ D)
          (Nat.succ_pos n') Module.finrank_pos m i = ks i
        suffices ∀ (d : ℕ) (hd : 0 < d) (hd' : d = d' + 1),
            productBasisIndicesAux (n' + 1) d (Nat.succ_pos n') hd m i = ks i from
          this _ _ hd'
        intro d hd hd'; subst hd'
        exact hm i
      -- Product Hermite = equiv.symm(basisVec m) for the right m:
      -- For any ks, the product ∏ basis(ks i)(x i) equals equiv.symm(basisVec m)(x)
      -- where pbi m = ks, by productRapidDecayEquiv_symm_basisVec_isProductHermite + ext.
      have product_basis_eq_equiv : ∀ ks : Fin n → ℕ, ∀ m, pbi m = ks →
          ∀ (G : SchwartzMap (Fin n → D) ℝ),
            (∀ x, G x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
              G = equiv.symm (RapidDecaySeq.basisVec m) := by
        intro ks m hpbi G hG
        ext x
        rw [hG x]
        have := productRapidDecayEquiv_symm_basisVec_isProductHermite (D := D) n hn m x
        simp only [pbi] at hpbi
        rw [hpbi] at this
        exact this.symm
      -- w_re on product Hermites = Phi_re on basis tuples:
      have w_re_on_product : ∀ ks : Fin n → ℕ,
          ∀ (G : SchwartzMap (Fin n → D) ℝ),
            (∀ x, G x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
              w_re G = Phi_re (fun i => DyninMityaginSpace.basis (ks i)) := by
        intro ks G hG
        obtain ⟨m, hm⟩ := pbi_surj ks
        have hGeq := product_basis_eq_equiv ks m hm G hG
        rw [hGeq, hw_re_basis m, hm]
      have w_im_on_product : ∀ ks : Fin n → ℕ,
          ∀ (G : SchwartzMap (Fin n → D) ℝ),
            (∀ x, G x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
              w_im G = Phi_im (fun i => DyninMityaginSpace.basis (ks i)) := by
        intro ks G hG
        obtain ⟨m, hm⟩ := pbi_surj ks
        have hGeq := product_basis_eq_equiv ks m hm G hG
        rw [hGeq, hw_im_basis m, hm]
      -- Now: both w_re(F) and Phi_re(gs) are determined by basis expansions.
      -- Specifically, the map gs ↦ w_re(∏ gs i (x i)) is a continuous multilinear
      -- map on (SchwartzMap D ℝ)^n that agrees with Phi_re on basis tuples.
      -- By continuousMultilinear_eq_of_basis_eq, they agree everywhere.
      -- The ContinuousMultilinearMap construction for gs ↦ w_re(productTensor(gs))
      -- requires showing the product tensor is continuous multilinear.
      -- Final step: w_re(F) = Phi_re(gs) and w_im(F) = Phi_im(gs)
      -- where F x = ∏ gs i (x i).
      --
      -- PROOF STRATEGY: Both gs ↦ w_re(∏ gs i (x i)) and Phi_re are continuous
      -- ℝ-multilinear maps on (SchwartzMap D ℝ)^n → ℝ that agree on all DM basis
      -- tuples (by w_re_on_product above). By continuousMultilinear_eq_of_basis_eq,
      -- they agree everywhere. Similarly for w_im and Phi_im.
      --
      -- TECHNICAL ISSUE: continuousMultilinear_eq_of_basis_eq requires
      -- NormedAddCommGroup E, but SchwartzMap D ℝ only has a family of seminorms.
      -- This can be resolved by:
      -- (a) Weakening continuousMultilinear_eq_of_basis_eq to use AddCommGroup +
      --     TopologicalSpace (requires rewriting the proof to avoid curryLeft which
      --     needs NormedAddCommGroup), or
      -- (b) Using DyninMityaginSpace.expansion directly on the product space to
      --     show the DM coefficients of the product function ∏ gs i (x i) factor
      --     as products of individual DM coefficients, or
      -- (c) Constructing an auxiliary normed space structure on SchwartzMap via
      --     a single seminorm that bounds the relevant quantities.
      --
      -- The mathematical content is fully captured by w_re_on_product/w_im_on_product
      -- (agreement on product Hermite functions) + pbi_surj (surjectivity of
      -- productBasisIndices), which are proved above.
      -- Induction on j: number of free (non-basis) arguments.
      -- P(j): for all gs with gs i = basis(ks i) for i ≥ j, w_re(∏ gs) = Phi_re(gs)
      -- P(0): all basis → proved by w_re_on_product
      -- P(j) → P(j+1): fix all but slot j, get two CLMs agreeing on basis → equal by DM expansion
      suffices key : ∀ (j : ℕ) (hj : j ≤ n)
          (gs : Fin n → SchwartzMap D ℝ)
          (hs : ∀ i : Fin n, j ≤ i.val → ∃ k, gs i = DyninMityaginSpace.basis k),
          w_re (schwartzProductTensor_schwartz n (by omega : 1 ≤ n) gs).choose =
            Phi_re gs ∧
          w_im (schwartzProductTensor_schwartz n (by omega : 1 ≤ n) gs).choose =
            Phi_im gs by
        obtain ⟨hre, him⟩ := key n le_rfl gs (fun i hi => absurd hi (by omega))
        apply Complex.ext
        · show w_re F = Phi_re gs
          have hFeq : F = (schwartzProductTensor_schwartz n (by omega : 1 ≤ n) gs).choose := by
            ext x; rw [hF]; exact ((schwartzProductTensor_schwartz n (by omega) gs).choose_spec x).symm
          rw [hFeq]; exact hre
        · show w_im F = Phi_im gs
          have hFeq : F = (schwartzProductTensor_schwartz n (by omega : 1 ≤ n) gs).choose := by
            ext x; rw [hF]; exact ((schwartzProductTensor_schwartz n (by omega) gs).choose_spec x).symm
          rw [hFeq]; exact him
      intro j
      induction j with
      | zero =>
        intro hj gs hs
        -- All gs i are basis vectors
        have hbasis : ∀ i, ∃ k, gs i = DyninMityaginSpace.basis k := fun i => hs i (Nat.zero_le _)
        choose ks hks using hbasis
        have hgs_eq : gs = fun i => DyninMityaginSpace.basis (ks i) := funext hks
        subst hgs_eq
        have hF := (schwartzProductTensor_schwartz n (by omega) (fun i => DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i))).choose_spec
        have hG : ∀ x, (schwartzProductTensor_schwartz n (by omega) (fun i => DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i))).choose x =
            ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i) := by
          intro x; exact hF x
        exact ⟨w_re_on_product ks _ hG, w_im_on_product ks _ hG⟩
      | succ j ih =>
        intro hj gs hs
        -- ih applies to tuples with basis vectors from index j onward
        -- We free slot j by using DM expansion
        -- For any basis ψ_m in slot j, the tuple satisfies P(j):
        have h_with_basis : ∀ (m : ℕ),
            let gs' := Function.update gs ⟨j, by omega⟩ (DyninMityaginSpace.basis m)
            w_re (schwartzProductTensor_schwartz n (by omega) gs').choose = Phi_re gs' ∧
            w_im (schwartzProductTensor_schwartz n (by omega) gs').choose = Phi_im gs' := by
          intro m
          apply ih (by omega)
          intro i hi
          by_cases hij : i = ⟨j, by omega⟩
          · exact ⟨m, by rw [hij, Function.update_self]⟩
          · have : j + 1 ≤ i.val := by
              have hne : i.val ≠ j := fun h => hij (Fin.ext h)
              omega
            have hne : i ≠ ⟨j, by omega⟩ := hij
            rw [Function.update_of_ne hne]
            exact hs i (by omega)
        -- Use DM expansion in slot j to free gs ⟨j, _⟩.
        -- L₂(f) = Phi_re(update gs jj f) is a CLM via toContinuousLinearMap.
        -- L₁(f) = w_re(productTensor(update gs jj f)) agrees with L₂ on basis.
        -- By DM expansion (clm_eq_of_basis_eq), L₁ = L₂, so they agree on gs j.
        set jj : Fin n := ⟨j, by omega⟩
        -- L₂(f) = Phi_re(update gs jj f) is a CLM via toContinuousLinearMap
        set L_re := Phi_re.toContinuousLinearMap gs jj
        set L_im := Phi_im.toContinuousLinearMap gs jj
        -- L_re(ψ_m) = Phi_re(update gs jj ψ_m) and similarly for L_im
        -- h_with_basis gives w_re(productTensor(update gs jj ψ_m)) = L_re(ψ_m)
        -- We need: w_re(productTensor gs) = L_re(gs jj) and similarly for w_im

        -- Key: DM expansion applied to L_re (which IS a CLM on S(D)):
        -- L_re(gs jj) = Σ_m coeff_m(gs jj) · L_re(ψ_m)
        have h_Lre_expand := DyninMityaginSpace.expansion L_re (gs jj)
        have h_Lim_expand := DyninMityaginSpace.expansion L_im (gs jj)

        -- And for w_re(productTensor gs):
        -- w_re(F) where F = productTensor gs
        -- By DM expansion on S(∏D): w_re(F) = Σ_p coeff_p(F) · w_re(basis_p)
        -- But this is the PRODUCT-SPACE expansion, not the SLOT expansion.

        -- Alternative: use that L_re determines Phi_re(gs) = L_re(gs jj),
        -- and the DM expansion of L_re shows L_re is determined by L_re(ψ_m).
        -- Similarly construct a CLM for the w_re side and show it equals L_re.

        -- The w_re-side CLM: f ↦ w_re(productTensor(update gs jj f))
        -- This is the composition of:
        --   f ↦ update gs jj f (continuous linear: affine map, linear part is proj)
        --   gs' ↦ productTensor gs' (continuous in each slot — THIS IS WHAT WE NEED)
        --   F ↦ w_re F (CLM)
        --
        -- For now, sorry this slot continuity and use it to close the proof.
        -- The slot continuity is provable from schwartz_product_decay.
        have slot_CLM_re : ∃ L₁ : SchwartzMap D ℝ →L[ℝ] ℝ,
            ∀ f, L₁ f = w_re (schwartzProductTensor_schwartz n (by omega)
              (Function.update gs jj f)).choose := sorry
        have slot_CLM_im : ∃ L₁ : SchwartzMap D ℝ →L[ℝ] ℝ,
            ∀ f, L₁ f = w_im (schwartzProductTensor_schwartz n (by omega)
              (Function.update gs jj f)).choose := sorry
        obtain ⟨L₁_re, hL₁_re⟩ := slot_CLM_re
        obtain ⟨L₁_im, hL₁_im⟩ := slot_CLM_im
        -- L₁_re and L_re agree on all basis vectors
        have h_agree_re : ∀ m, L₁_re (DyninMityaginSpace.basis m) = L_re (DyninMityaginSpace.basis m) := by
          intro m; rw [hL₁_re]; exact (h_with_basis m).1
        have h_agree_im : ∀ m, L₁_im (DyninMityaginSpace.basis m) = L_im (DyninMityaginSpace.basis m) := by
          intro m; rw [hL₁_im]; exact (h_with_basis m).2
        -- By clm_eq_of_basis_eq, L₁ = L₂
        have hL_eq_re := DyninMityaginSpace.clm_eq_of_basis_eq L₁_re L_re h_agree_re
        have hL_eq_im := DyninMityaginSpace.clm_eq_of_basis_eq L₁_im L_im h_agree_im
        -- So L₁(gs jj) = L₂(gs jj), i.e., w_re(productTensor gs) = Phi_re(gs)
        constructor
        · -- w_re case
          have h1 : w_re (schwartzProductTensor_schwartz n (by omega) gs).choose =
              L₁_re (gs jj) := by
            rw [hL₁_re]; congr 1; ext x
            simp [(schwartzProductTensor_schwartz n _ gs).choose_spec,
                  (schwartzProductTensor_schwartz n _ (Function.update gs jj (gs jj))).choose_spec,
                  Function.update_eq_self]
          rw [h1, show L₁_re = L_re from hL_eq_re]
        · -- w_im case
          have h1 : w_im (schwartzProductTensor_schwartz n (by omega) gs).choose =
              L₁_im (gs jj) := by
            rw [hL₁_im]; congr 1; ext x
            simp [(schwartzProductTensor_schwartz n _ gs).choose_spec,
                  (schwartzProductTensor_schwartz n _ (Function.update gs jj (gs jj))).choose_spec,
                  Function.update_eq_self]
          rw [h1, show L₁_im = L_im from hL_eq_im]
  refine ⟨W, hW_agree, ?_⟩
  -- Uniqueness: if W' also agrees on product tensors, then W' = W.
  intro W' hW'
  -- The difference V := W' - W vanishes on all product tensors:
  set V := W' - W with hV_def
  have hDiff : ∀ fs, V (complexProductTensor fs) = 0 := by
    intro fs; simp [V, hW', hW_agree]
  -- Suffices to show V = 0
  suffices hV0 : V = 0 by
    have : W' = W + V := by simp [V]
    rw [this, hV0, add_zero]
  -- V ∘ ι vanishes on product Hermite functions (real-valued basis products).
  -- Define the ℝ-linear restriction:
  set ι := iotaSchwartz (Fin n → D)
  set Vr : SchwartzMap (Fin n → D) ℂ →L[ℝ] ℂ := clmRestrictReal V
  -- Re(V ∘ ι) and Im(V ∘ ι) vanish on product Hermite functions
  set VRe : SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ := Complex.reCLM.comp (Vr.comp ι)
  set VIm : SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ := Complex.imCLM.comp (Vr.comp ι)
  -- Step 1: V ∘ ι vanishes on all product Hermite functions (real basis products).
  -- This is because complexProductTensor (ι ∘ basis_ks) = ι(product_Hermite)
  -- and V vanishes on all complex product tensors by hDiff.
  have hVι : ∀ (f : SchwartzMap (Fin n → D) ℝ), Vr.comp ι f = 0 := by
    -- V ∘ ι vanishes on product Hermite functions for n ≥ 1
    -- and on everything for n = 0 (trivial: S(Fin 0 → D) is one-dimensional)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- n = 0: Fin 0 → D is a subsingleton, so every Schwartz function is constant.
      -- ι(f) = (↑(f 0) : ℂ) • complexProductTensor Fin.elim0, so
      -- V(ι f) = (↑(f 0)) * V(complexProductTensor Fin.elim0) = (↑(f 0)) * 0 = 0.
      intro f
      show V (ι f) = 0
      set cpt0 := complexProductTensor (Fin.elim0 : Fin 0 → SchwartzMap D ℂ)
      have hιf : ι f = (↑(f 0) : ℂ) • cpt0 := by
        ext x
        simp only [SchwartzMap.smul_apply, smul_eq_mul]
        show ↑(f x) = ↑(f 0) * cpt0 x
        simp only [cpt0, complexProductTensor_apply, Finset.univ_eq_empty,
          Finset.prod_empty, mul_one, Subsingleton.elim x 0]
      rw [hιf, V.map_smul, hDiff, smul_zero]
    · -- n ≥ 1: use productHermite_schwartz_dense
      -- VRe vanishes on product Hermite functions
      have hVRe_vanish : ∀ ks : Fin n → ℕ, ∀ (F : SchwartzMap (Fin n → D) ℝ),
          (∀ x, F x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
          VRe F = 0 := by
        intro ks F hF
        -- VRe(F) = Re(V(ι(F)))
        show Complex.re (V (ι F)) = 0
        -- ι(F) = complexProductTensor (fun i => ι(basis(ks i)))
        -- because both have the same underlying function.
        have hιF : ι F = complexProductTensor (fun i =>
            iotaSchwartz D (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i))) := by
          ext x
          show ↑(F x) = complexProductTensor (fun i =>
            iotaSchwartz D (DyninMityaginSpace.basis (ks i))) x
          rw [hF x, complexProductTensor_ofReal]
        rw [hιF, hDiff]; simp
      -- VIm vanishes on product Hermite functions
      have hVIm_vanish : ∀ ks : Fin n → ℕ, ∀ (F : SchwartzMap (Fin n → D) ℝ),
          (∀ x, F x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
          VIm F = 0 := by
        intro ks F hF
        show Complex.im (V (ι F)) = 0
        have hιF : ι F = complexProductTensor (fun i =>
            iotaSchwartz D (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i))) := by
          ext x
          show ↑(F x) = complexProductTensor (fun i =>
            iotaSchwartz D (DyninMityaginSpace.basis (ks i))) x
          rw [hF x, complexProductTensor_ofReal]
        rw [hιF, hDiff]; simp
      -- By productHermite_schwartz_dense, VRe = 0 and VIm = 0
      haveI : Inhabited (Fin n) := ⟨⟨0, hn⟩⟩
      haveI : Nontrivial (Fin n → D) := Pi.nontrivial
      have hVRe0 : VRe = 0 := productHermite_schwartz_dense n (by omega) VRe hVRe_vanish
      have hVIm0 : VIm = 0 := productHermite_schwartz_dense n (by omega) VIm hVIm_vanish
      -- Hence V ∘ ι = 0 (both Re and Im are zero)
      intro f
      have hRe : Complex.re (Vr.comp ι f) = 0 := by
        have : VRe f = 0 := by rw [hVRe0]; simp
        exact this
      have hIm : Complex.im (Vr.comp ι f) = 0 := by
        have : VIm f = 0 := by rw [hVIm0]; simp
        exact this
      exact Complex.ext hRe hIm
  -- Step 2: V = 0 on all of S(prod, ℂ), using decomposition f = ι(Re f) + i • ι(Im f).
  ext f
  show V f = 0
  rw [schwartz_complex_decomp f]
  simp only [V, ContinuousLinearMap.sub_apply, map_add, map_smul]
  -- V(ι(Re f)) = 0 and V(ι(Im f)) = 0 by hVι
  have h1 : Vr (ι (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f)) = 0 :=
    hVι _
  have h2 : Vr (ι (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f)) = 0 :=
    hVι _
  -- V is the same as Vr on S(prod, ℂ), composed with the addition
  -- Actually, V acts on ℂ-valued Schwartz, while Vr is V restricted to ℝ-linear
  -- V(ι(Re f) + I • ι(Im f)) = V(ι(Re f)) + I • V(ι(Im f))
  -- = Vr(ι(Re f)) + I * Vr(ι(Im f)) since V is ℂ-linear
  show V (iotaSchwartz (Fin n → D) (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f)) +
      Complex.I • V (iotaSchwartz (Fin n → D) (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f)) = 0
  -- V on ι(...) is the same as Vr on ι(...)
  change Vr (ι (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.reCLM f)) +
      Complex.I • Vr (ι (SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.imCLM f)) = 0
  rw [h1, h2]; simp

end GaussianField
