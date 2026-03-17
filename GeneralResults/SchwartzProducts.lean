/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results for Schwartz Nuclear Extension

Results about products of Schwartz functions, used in the nuclear extension theorem.

`schwartzProductTensor_schwartz` proves that the product tensor
`x ↦ ∏ᵢ fs i (x i)` is Schwartz on `Fin n → D` given Schwartz functions `fs i` on `D`.

Smoothness: `contDiff_prod` (product of smooth functions in separate variables is smooth).
Decay: `norm_iteratedFDeriv_prod_le` (Leibniz rule) combined with the chain rule
for `f ∘ proj_i` and Schwartz decay of each factor, using the distribution of
`‖x‖^k` across factors via `pi_norm_pow_le_sum`.

`productHermite_schwartz_dense` is a standard density result (Reed-Simon V.13).
-/

import SchwartzNuclear.HermiteNuclear
import SchwartzNuclear.SchwartzTensorProduct
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section

open GaussianField Finset

set_option maxHeartbeats 1600000

namespace GaussianField

/-! ## Auxiliary lemmas for product Schwartz decay -/

/-- `∏ᵢ (1 + aᵢ) ≥ 1 + ∑ᵢ aᵢ` for nonneg `aᵢ`. Standard inequality by induction. -/
private lemma prod_one_add_ge_one_add_sum {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    1 + ∑ i, a i ≤ ∏ i, (1 + a i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc]
    have ha' : ∀ i : Fin n, 0 ≤ a (Fin.castSucc i) := fun i => ha _
    have hih := ih (fun i => a (Fin.castSucc i)) ha'
    have hprod : 1 ≤ ∏ i : Fin n, (1 + a (Fin.castSucc i)) :=
      Finset.one_le_prod (fun i _ => by linarith [ha' i])
    linarith [le_mul_of_one_le_left (ha (Fin.last n)) hprod, mul_comm
      (∏ i : Fin n, (1 + a (Fin.castSucc i))) (1 + a (Fin.last n))]

/-- For the pi-sup-norm, `‖x‖^k ≤ ∑ᵢ ‖x i‖^k`. The sup is achieved at some component,
so `‖x‖^k` equals one of the terms and is bounded by the full sum. -/
private lemma pi_norm_pow_le_sum {n : ℕ} {D : Type*} [NormedAddCommGroup D]
    (x : Fin n → D) (k : ℕ) (hn : 0 < n) :
    ‖x‖ ^ k ≤ ∑ i : Fin n, ‖x i‖ ^ k := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne (fun i => ‖x i‖₊)
  have h_norm : ‖x‖ = ‖x j‖ := by
    rw [Pi.norm_def]
    exact congr_arg NNReal.toReal
      (show Finset.univ.sup (fun b => ‖x b‖₊) = ‖x j‖₊ from by
        rw [← Finset.sup'_eq_sup hne]; exact hj)
  rw [h_norm]
  exact single_le_sum (f := fun i => ‖x i‖ ^ k) (fun i _ => by positivity) (mem_univ j)

/-- Distribution of `‖x‖^k` across a product of nonneg functions on separate variables.
Key technique: `‖x‖^k ≤ ∑ᵢ ‖xᵢ‖^k`, then absorb each `‖xᵢ‖^k` into the i-th factor
using its k-decay bound, while bounding the remaining factors by their 0-decay bounds. -/
private lemma norm_pow_mul_prod_le
    {D : Type*} [NormedAddCommGroup D]
    {n : ℕ} (hn : 0 < n) (k : ℕ)
    (a : Fin n → D → ℝ) (ha_nn : ∀ j y, 0 ≤ a j y)
    (hbound0 : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : D, a j y ≤ C)
    (hboundk : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : D, ‖y‖ ^ k * a j y ≤ C) :
    ∃ C : ℝ, ∀ x : Fin n → D, ‖x‖ ^ k * ∏ j, a j (x j) ≤ C := by
  choose C0 hC0_nn hC0 using hbound0
  choose Ck hCk_nn hCk using hboundk
  exact ⟨∑ i, Ck i * ∏ j ∈ univ.erase i, C0 j, fun x =>
    calc ‖x‖ ^ k * ∏ j, a j (x j)
        ≤ (∑ i, ‖x i‖ ^ k) * ∏ j, a j (x j) :=
          mul_le_mul_of_nonneg_right (pi_norm_pow_le_sum x k hn)
            (prod_nonneg fun j _ => ha_nn j (x j))
      _ = ∑ i, ((‖x i‖ ^ k * a i (x i)) * ∏ j ∈ univ.erase i, a j (x j)) := by
          rw [sum_mul]; congr 1; ext i; rw [← mul_prod_erase _ _ (mem_univ i)]; ring
      _ ≤ ∑ i, (Ck i * ∏ j ∈ univ.erase i, C0 j) :=
          sum_le_sum fun i _ => mul_le_mul (hCk i (x i))
            (prod_le_prod (fun j _ => ha_nn j (x j)) (fun j _ => hC0 j (x j)))
            (prod_nonneg fun j _ => ha_nn j (x j)) (hCk_nn i)⟩

/-! ## Smoothness and chain rule for f ∘ proj -/

/-- The projection `fun x : Fin n → D => x i` composed with a Schwartz function
is smooth on the product domain. -/
private lemma contDiff_schwartz_comp_proj
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (f : SchwartzMap D ℝ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → D => f (x i)) :=
  f.smooth'.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => D) i).contDiff.of_le le_top)

/-- Norm bound for the iterated Fréchet derivative of `f ∘ proj_i`.
Using the chain rule for CLMs: `iteratedFDeriv (f ∘ L) x = (iteratedFDeriv f (L x)).compCLM L`,
and `‖compCLM L‖ ≤ ‖original‖ * ‖L‖^m ≤ ‖original‖` since `‖proj_i‖ ≤ 1`. -/
private lemma norm_iteratedFDeriv_comp_proj_le
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (f : SchwartzMap D ℝ) (i : Fin n) (m : ℕ) (x : Fin n → D) :
    ‖iteratedFDeriv ℝ m (fun x : Fin n → D => f (x i)) x‖ ≤
      ‖iteratedFDeriv ℝ m f (x i)‖ := by
  set L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => D) i
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y; simp [one_mul]; exact norm_le_pi_norm y i
  -- The composed function agrees definitionally with f.toFun ∘ L
  show ‖iteratedFDeriv ℝ m (f.toFun ∘ ⇑L) x‖ ≤ ‖iteratedFDeriv ℝ m f.toFun (x i)‖
  rw [L.iteratedFDeriv_comp_right f.smooth' x (i := m)
    (show (↑↑m : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) from by exact_mod_cast le_top)]
  calc ‖(iteratedFDeriv ℝ m f.toFun (L x)).compContinuousLinearMap fun _ => L‖
      ≤ ‖iteratedFDeriv ℝ m f.toFun (L x)‖ * ∏ _ : Fin m, ‖L‖ :=
        (iteratedFDeriv ℝ m f.toFun (L x)).norm_compContinuousLinearMap_le _
    _ ≤ ‖iteratedFDeriv ℝ m f.toFun (L x)‖ * 1 := by
        gcongr; exact prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL)
    _ = ‖iteratedFDeriv ℝ m f.toFun (x i)‖ := by simp [L]

/-! ## Product of Schwartz functions is Schwartz -/

/-- **Schwartz decay for the product `∏ᵢ fs i (x i)` on the product domain.**

The proof combines three ingredients:
1. **Leibniz rule** (`norm_iteratedFDeriv_prod_le`): the m-th derivative of a product
   is bounded by a sum over derivative distributions of products of individual derivatives.
2. **Chain rule** (`norm_iteratedFDeriv_comp_proj_le`): derivatives of `fs i ∘ proj_i`
   are bounded by derivatives of `fs i` evaluated at `x i`.
3. **Distribution of ‖x‖^k** (`norm_pow_mul_prod_le`): using `‖x‖^k ≤ ∑ᵢ ‖xᵢ‖^k`,
   absorb the polynomial weight into one factor's Schwartz decay bound while bounding
   the remaining factors by their sup norms.

The formal proof applies the Leibniz rule to reduce to a finite sum of products,
bounds each product factor via the chain rule, then applies `norm_pow_mul_prod_le`
to handle the `‖x‖^k` weight. Since the Leibniz sum is finite with constant
coefficients, the result is bounded. -/
private lemma schwartz_product_decay
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (n : ℕ) (hn : 0 < n) (fs : Fin n → SchwartzMap D ℝ) (k m : ℕ) :
    ∃ C, ∀ x : Fin n → D,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => ∏ i, fs i (x i)) x‖ ≤ C := by
  -- Smoothness of each component
  have hsmooth : ∀ i : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → D => fs i (x i)) :=
    fun i => contDiff_schwartz_comp_proj (fs i) i
  -- Abbreviation for cast
  have hm : (↑↑m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  -- Step 1: For each derivative distribution p ∈ sym m, bound the corresponding term.
  -- Each term has the form: multinomial(p) * ∏ⱼ ‖iteratedFDeriv (cⱼ) (fs j ∘ proj j) x‖
  -- where cⱼ = Multiset.count j p.
  -- By the chain rule: each factor ≤ ‖iteratedFDeriv (cⱼ) (fs j) (x j)‖.
  -- Then ‖x‖^k * ∏ⱼ ‖iteratedFDeriv (cⱼ) (fs j) (x j)‖ is bounded by norm_pow_mul_prod_le.

  -- For each p, get the bound from norm_pow_mul_prod_le
  have h_term_bound : ∀ (c : Fin n → ℕ),
      ∃ Cp, 0 ≤ Cp ∧ ∀ x : Fin n → D,
        ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x : Fin n → D => fs j (x j)) x‖ ≤ Cp := by
    intro c
    -- Bound each factor using chain rule, then apply norm_pow_mul_prod_le
    have h_chain_prod : ∀ x : Fin n → D,
        ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x : Fin n → D => fs j (x j)) x‖ ≤
          ∏ j, ‖iteratedFDeriv ℝ (c j) (fs j) (x j)‖ :=
      fun x => prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => norm_iteratedFDeriv_comp_proj_le (fs j) j (c j) x)
    -- Apply the distribution bound
    obtain ⟨Cp, hCp⟩ := norm_pow_mul_prod_le hn k
      (fun j y => ‖iteratedFDeriv ℝ (c j) (fs j) y‖) (fun j y => norm_nonneg _)
      (fun j => by
        obtain ⟨C, hC⟩ := (fs j).decay' 0 (c j)
        exact ⟨C, le_trans (by positivity) (hC 0), fun y => by simpa using hC y⟩)
      (fun j => by
        obtain ⟨C, hC⟩ := (fs j).decay' k (c j)
        exact ⟨C, le_trans (by positivity) (hC 0), hC⟩)
    exact ⟨Cp, le_trans (by positivity) (hCp 0), fun x =>
      calc ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (fun x => fs j (x j)) x‖
          ≤ ‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (c j) (fs j) (x j)‖ :=
            mul_le_mul_of_nonneg_left (h_chain_prod x) (by positivity)
        _ ≤ Cp := hCp x⟩
  -- Step 2: Use norm_iteratedFDeriv_prod_le and sum the per-term bounds
  -- First, use Classical.choice to select bounds for each p ∈ sym m
  -- (we only need bounds for the derivative distributions that appear)
  -- Since sym m is finite, sum them up.
  -- For each p, the count function c_p : Fin n → ℕ satisfies ∑ c_p j = m
  have h_deriv : ∀ x : Fin n → D,
      ‖iteratedFDeriv ℝ m (fun x => ∏ i, fs i (x i)) x‖ ≤
        ∑ p ∈ univ.sym m,
          ↑(p.val).multinomial *
            ∏ j, ‖iteratedFDeriv ℝ (p.val.count j)
              (fun x : Fin n → D => fs j (x j)) x‖ :=
    fun x => norm_iteratedFDeriv_prod_le (fun i _ => hsmooth i) (x := x) (n := m) hm
  -- Now: ‖x‖^k * ‖D^m(∏...)x‖ ≤ ‖x‖^k * ∑_p ...
  -- = ∑_p (multinomial(p) * (‖x‖^k * ∏_j ‖D^{c_j}(...)x‖))
  -- Actually we need to commute the ‖x‖^k inside the sum.
  -- Each term is bounded by multinomial(p) * Cp.

  -- Choose bounds for each p
  choose Cp hCp_nn hCp using fun (p : Sym (Fin n) m) => h_term_bound (fun j => p.val.count j)
  refine ⟨∑ p ∈ univ.sym m, ↑(p.val).multinomial * Cp p, fun x => ?_⟩
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => ∏ i, fs i (x i)) x‖
      ≤ ‖x‖ ^ k * ∑ p ∈ univ.sym m,
          ↑(p.val).multinomial *
            ∏ j, ‖iteratedFDeriv ℝ (p.val.count j) (fun x => fs j (x j)) x‖ :=
        mul_le_mul_of_nonneg_left (h_deriv x) (by positivity)
    _ = ∑ p ∈ univ.sym m, (↑(p.val).multinomial *
          (‖x‖ ^ k * ∏ j, ‖iteratedFDeriv ℝ (p.val.count j)
            (fun x => fs j (x j)) x‖)) := by
        rw [mul_sum]; congr 1; ext p; ring
    _ ≤ ∑ p ∈ univ.sym m, (↑(p.val).multinomial * Cp p) := by
        apply sum_le_sum; intro p _
        apply mul_le_mul_of_nonneg_left (hCp p x)
        exact Nat.cast_nonneg _

/-- **Product of Schwartz functions is Schwartz.**

Given `n` Schwartz functions `fs : Fin n → SchwartzMap D ℝ` on a finite-dimensional `D`,
the product function `x ↦ ∏ᵢ fs i (x i)` is Schwartz on `Fin n → D`.

Constructed directly by providing the `toFun`, `smooth'` and `decay'` fields.
- **Smoothness**: `contDiff_prod` — each `x ↦ fs i (x i)` is smooth (composition of
  Schwartz with the smooth linear projection), so the finite product is smooth.
- **Decay**: `schwartz_product_decay` — combines the Leibniz rule for iterated derivatives
  of products (`norm_iteratedFDeriv_prod_le`), the chain rule norm bound for `f ∘ proj_i`
  (`norm_iteratedFDeriv_comp_proj_le`), and distribution of the `‖x‖^k` weight across
  factors (`norm_pow_mul_prod_le`). -/
theorem schwartzProductTensor_schwartz
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n) (fs : Fin n → SchwartzMap D ℝ) :
    haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin n → D) := Pi.nontrivial
    ∃ (F : SchwartzMap (Fin n → D) ℝ), ∀ x, F x = ∏ i, fs i (x i) := by
  haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin n → D) := Pi.nontrivial
  refine ⟨⟨fun x => ∏ i, fs i (x i), ?smooth, ?decay⟩, fun x => rfl⟩
  case smooth =>
    exact contDiff_prod (fun i _ => contDiff_schwartz_comp_proj (fs i) i)
  case decay =>
    intro k m
    exact schwartz_product_decay n (by omega) fs k m

/-! ## Density of product Hermite functions -/

/-- A continuous linear functional on a DyninMityaginSpace that vanishes on all basis
elements is zero. Immediate from the DM expansion `φ f = ∑' m, coeff_m(f) * φ(basis_m)`. -/
private lemma clm_zero_of_basis_zero {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [DyninMityaginSpace E]
    (φ : E →L[ℝ] ℝ)
    (h : ∀ m : ℕ, φ (DyninMityaginSpace.basis m) = 0) :
    φ = 0 := by
  ext f; rw [DyninMityaginSpace.expansion φ f]; simp [h]

/-- Product Hermite functions are dense in Schwartz space on the product domain.

If a continuous linear functional on `S(∏D)` vanishes on all product Hermite functions,
it is zero.

**Proof** (by induction on `n`):

*Base case* (`n = 1`): The product Hermite functions `∏ i : Fin 1, ψ_{k i}(x i)`
reduce to `ψ_{k 0}(x 0)`. Via the continuous linear equivalence
`Fin 1 → D ≃L[ℝ] D` (`ContinuousLinearEquiv.funUnique`), the Schwartz domain
transfer `schwartzDomCongr` sends each DM basis element `ψ_m` of `S(D)` to the
function `x ↦ ψ_m(x 0)` on `S(Fin 1 → D)`. The hypothesis gives `φ(T(ψ_m)) = 0`,
i.e., `(φ ∘ T)(ψ_m) = 0` for all `m`. By the DM expansion
(`clm_zero_of_basis_zero`), `φ ∘ T = 0`. Since `T` is an equivalence, `φ = 0`.

*Inductive step* (`n → n+1`): Uses currying through the splitting
`Fin (n+1) → D ≃L[ℝ] D × (Fin n → D)`. For each product Hermite `G` on the
last `n` variables, define `φ_G : S(D) →L[ℝ] ℝ` by `φ_G(f) = φ(f ⊗ G)`.
The hypothesis gives `φ_G(ψ_k) = 0` for all `k`, so `φ_G = 0` by the base case.
Then for any `f`, the functional `g ↦ φ(f ⊗ g)` vanishes on all product Hermites
on `n` variables, hence is zero by the induction hypothesis. Pure tensors are dense
in `S(Fin (n+1) → D)` (Schwartz kernel theorem), so `φ = 0`.

The currying CLM construction (showing `f ↦ φ(f ⊗ G)` is continuous linear)
requires Schwartz seminorm estimates on the bilinear tensor product, using
the same decay bounds as `schwartz_product_decay`.

Ref: Reed-Simon I, Theorem V.13; Gel'fand-Vilenkin IV §3. -/
theorem productHermite_schwartz_dense
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n)
    (φ : haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
         haveI : Nontrivial (Fin n → D) := Pi.nontrivial
         SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ)
    (hφ : ∀ ks : Fin n → ℕ, ∀ (F : SchwartzMap (Fin n → D) ℝ),
      (∀ x, F x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
      φ F = 0) :
    φ = 0 := by
  haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI : Nontrivial (Fin n → D) := Pi.nontrivial
  induction n with
  | zero => omega
  | succ k ih =>
    by_cases hk : k = 0
    · -- **Base case n = 1**: Transfer via CLE (Fin 1 → D) ≃L[ℝ] D.
      subst hk
      -- schwartzDomCongr sends S(D) → S(Fin 1 → D) via f ↦ (x ↦ f(x 0))
      set T : SchwartzMap D ℝ ≃L[ℝ] SchwartzMap (Fin 1 → D) ℝ :=
        schwartzDomCongr (ContinuousLinearEquiv.funUnique (Fin 1) ℝ D)
      -- Compose: φ' = φ ∘ T : S(D) →L[ℝ] ℝ
      set φ' : SchwartzMap D ℝ →L[ℝ] ℝ := φ.comp T.toContinuousLinearMap
      -- φ' vanishes on all DM basis elements of S(D):
      -- φ'(ψ_m) = φ(T(ψ_m)) and T(ψ_m)(x) = ψ_m(x 0) = ∏ i : Fin 1, ψ_m(x i)
      have h_basis : ∀ m, φ' (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m) = 0 := by
        intro m
        show φ (T (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m)) = 0
        apply hφ (fun _ => m) (T (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m))
        intro x
        simp [T, schwartzDomCongr, SchwartzMap.compCLMOfContinuousLinearEquiv]
      -- By DM expansion, φ' = 0
      have hφ'_zero : φ' = 0 := clm_zero_of_basis_zero φ' h_basis
      -- Since T is an equivalence (surjective), φ = 0
      ext f
      have key : φ' (T.symm f) = 0 := by simp [hφ'_zero]
      simp only [φ', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        T.apply_symm_apply] at key
      simpa using key
    · -- **Inductive step n = k + 1, k ≥ 1**:
      -- The proof requires currying CLMs and density of pure tensors.
      -- (1) Currying: for fixed product Hermite G on S(Fin k → D),
      --     f ↦ φ(f ⊗ G) must be shown to be a CLM from S(D) to ℝ.
      --     This needs joint continuity of the bilinear tensor product map
      --     S(D) × S(Fin k → D) → S(Fin (k+1) → D).
      -- (2) Density: pure tensors f ⊗ g span S(Fin (k+1) → D) in the
      --     Schwartz topology, which follows from the Schwartz kernel theorem.
      -- Both are mathematically standard (Reed-Simon V.13) but require
      -- significant formalization infrastructure.
      sorry

end GaussianField
