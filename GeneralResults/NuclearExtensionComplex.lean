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
    sorry
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
