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

set_option maxHeartbeats 3200000

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

/-- Currying as a continuous linear equivalence on finite function spaces. -/
private noncomputable def curryCLE (n d : ℕ) :
    ((Fin n × Fin d) → ℝ) ≃L[ℝ] (Fin n → Fin d → ℝ) := by
  refine ContinuousLinearEquiv.mk (LinearEquiv.curry ℝ ℝ (Fin n) (Fin d)) ?_ ?_
  · simpa [LinearEquiv.curry, Function.curry] using
      (continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j))
  · simpa [LinearEquiv.curry, Function.uncurry] using
      (continuous_pi fun p : Fin n × Fin d =>
        ((continuous_apply p.2).comp (continuous_apply p.1)))

/-- Flatten a finite family of Euclidean blocks into one Euclidean space. -/
noncomputable def flattenEuclidean (n d : ℕ) :
    (Fin n → EuclideanSpace ℝ (Fin d)) ≃L[ℝ] EuclideanSpace ℝ (Fin (n * d)) := by
  let e1 := ContinuousLinearEquiv.piCongrRight
    (fun _ : Fin n => EuclideanSpace.equiv (Fin d) ℝ)
  let e2 := (curryCLE n d).symm
  let e3 := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (n * d) => ℝ)
    (finProdFinEquiv : Fin n × Fin d ≃ Fin (n * d))
  exact e1.trans (e2.trans (e3.trans (EuclideanSpace.equiv (Fin (n * d)) ℝ).symm))

/-- Product-aware Euclidean coordinates on `Fin n → D`, flattening each `toEuclidean D`
block contiguously. -/
noncomputable def prodToEuclidean (n : ℕ) (D : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] :
    (Fin n → D) ≃L[ℝ] EuclideanSpace ℝ (Fin (n * Module.finrank ℝ D)) := by
  exact (ContinuousLinearEquiv.piCongrRight
      (fun _ : Fin n => toEuclidean (E := D))).trans
    (flattenEuclidean n (Module.finrank ℝ D))

/-- Restrict a total multi-index on `Fin (n * d)` to the `i`-th block of length `d`. -/
noncomputable def blockMultiIndex (n d : ℕ) (α : Fin (n * d) → ℕ) (i : Fin n) :
    Fin d → ℕ :=
  fun j => α (finProdFinEquiv (i, j))

/-- `schwartzRapidDecayEquivFin d hd` inverse applied to `basisVec m` yields the
multi-dimensional Hermite function `hermiteFunctionNd d α` where `α` is the multi-index
corresponding to `m` via `multiIndexEquiv`. Handles both `d = 1` and `d ≥ 2` cases. -/
private lemma equivFin_symm_basisVec (d : ℕ) (hd : 0 < d) (m : ℕ)
    (y : EuclideanSpace ℝ (Fin d)) :
    ((schwartzRapidDecayEquivFin d hd).symm (RapidDecaySeq.basisVec m)) y =
    hermiteFunctionNd d (Nat.succ_pred_eq_of_pos hd ▸ (multiIndexEquiv (d - 1)).symm m) y := by
  rcases d with _ | _ | d'
  · omega
  · simp only [schwartzRapidDecayEquivFin, ContinuousLinearEquiv.symm_trans_apply,
      ContinuousLinearEquiv.symm_symm, schwartzDomCongr,
      ContinuousLinearEquiv.equivOfInverse_apply,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
    rw [schwartzRapidDecayEquiv1D_symm_apply]
    simp [RapidDecaySeq.basisVec, hermiteFunctionNd, multiIndexEquiv, euclideanFin1Equiv]
  · simp only [schwartzRapidDecayEquivFin]
    rw [schwartzRapidDecayEquivNd_symm_apply]
    simp [RapidDecaySeq.basisVec]; rfl

/-- Cast roundtrip: applying `multiIndexEquiv.symm ∘ multiIndexEquiv` to a Fin-cast
multi-index and casting back recovers the original. Uses proof irrelevance and
the fact that `d - 1 + 1 = d` is definitional for `d = d' + 1`. -/
private lemma cast_equiv_roundtrip (d : ℕ) (hd : 0 < d) (β : Fin d → ℕ) :
    (Nat.succ_pred_eq_of_pos hd ▸
      (multiIndexEquiv (d - 1)).symm ((multiIndexEquiv (d - 1))
        (Nat.succ_pred_eq_of_pos hd ▸ β)) : Fin d → ℕ) = β := by
  rw [Equiv.symm_apply_apply]
  rcases d with _ | d'; · omega
  change β = β; rfl

/-- **Product-aware CLE from `S(Fin n → D)` to `RapidDecaySeq`.**

Unlike the canonical `schwartzRapidDecayEquiv (Fin n → D)` which goes through an
AoC-chosen `toEuclidean` that may not respect the product structure, this equivalence
uses `prodToEuclidean` which applies `toEuclidean` per component. This ensures that
the resulting Hermite basis elements factor as products of per-factor DM basis elements. -/
noncomputable def productRapidDecayEquiv
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    (n : ℕ) (hn : 0 < n) :
    SchwartzMap (Fin n → D) ℝ ≃L[ℝ] RapidDecaySeq := by
  have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
  have hnd : 0 < n * Module.finrank ℝ D := Nat.mul_pos hn hd
  exact (schwartzDomCongr (prodToEuclidean n D)).symm.trans
    (schwartzRapidDecayEquivFin (n * Module.finrank ℝ D) hnd)

/-- The factor-space basis indices corresponding to the `m`-th basis vector of the
product-aware rapid-decay equivalence. -/
noncomputable def productBasisIndices
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    (n : ℕ) (hn : 0 < n) (m : ℕ) : Fin n → ℕ := by
  let d := Module.finrank ℝ D
  have hd : 0 < d := Module.finrank_pos
  let N := n * d
  have hN : 0 < N := Nat.mul_pos hn hd
  let α : Fin N → ℕ := Nat.succ_pred_eq_of_pos hN ▸ (multiIndexEquiv (N - 1)).symm m
  exact fun i => (multiIndexEquiv (d - 1))
    (Nat.succ_pred_eq_of_pos hd ▸ blockMultiIndex n d α i)

/-- A block multi-index has `abs` bounded by the total multi-index `abs`. -/
lemma blockMultiIndex_abs_le
    (n d : ℕ) (α : Fin (n * d) → ℕ) (i : Fin n) :
    (MultiIndex.abs (blockMultiIndex n d α i) : ℝ) ≤ MultiIndex.abs α := by
  classical
  let s : Finset (Fin (n * d)) := Finset.univ.image (fun j : Fin d => finProdFinEquiv (i, j))
  have hs :
      (∑ j : Fin d, α (finProdFinEquiv (i, j))) = Finset.sum s α := by
    unfold s
    rw [Finset.sum_image]
    intro a _ b _ hab
    have hpair : (i, a) = (i, b) := finProdFinEquiv.injective hab
    simpa using congrArg Prod.snd hpair
  have hnat : MultiIndex.abs (blockMultiIndex n d α i) ≤ MultiIndex.abs α := by
    simp [MultiIndex.abs, blockMultiIndex, hs]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro x hx; simp)
      (fun _ _ _ => Nat.zero_le _)
  exact_mod_cast hnat

/-- Generic polynomial growth for the multiIndexEquiv ∘ blockMultiIndex ∘ multiIndexEquiv.symm chain.
This is the core bound, stated without reference to `Module.finrank`. -/
-- The growth bound works abstractly: for any value that equals
-- multiIndexEquiv(d-1)(cast ▸ blockMultiIndex n d (cast ▸ multiIndexEquiv(N-1).symm m) i),
-- it is bounded by C * (1+m)^q. We don't need to unfold productBasisIndices at all.
-- Instead, we prove that productBasisIndices m i = some value v, and bound v.
-- The key: productBasisIndices is DEFINED as exactly this chain, so `rfl` gives the equality
-- when Module.finrank ℝ D is concrete. But since it's abstract, we use `change` to
-- rewrite the goal to the chain applied to Module.finrank ℝ D.
--
-- Actually, the simplest fix: add productBasisIndices as an OPAQUE bound.
-- We know 1 + pbi m i ≤ bound, because pbi is defined as multiIndexEquiv ∘ blockMultiIndex ∘ multiIndexEquiv.symm.
-- The bound follows regardless of what Module.finrank is — it only needs d > 0.
-- Core bound for successor dimensions: no Nat.succ_pred casts.
private theorem generic_pbi_bound (n' d' : ℕ) :
    ∃ C > 0, ∃ q : ℕ, ∀ (m : ℕ) (i : Fin (n' + 1)),
      let α := (multiIndexEquiv ((n' + 1) * (d' + 1) - 1)).symm m
      ((multiIndexEquiv d') (blockMultiIndex (n' + 1) (d' + 1) α i) : ℝ) ≤
        C * (1 + (m : ℝ)) ^ q := by
  obtain ⟨C₁, hC₁, k₁, h_symm⟩ := multiIndexEquiv_symm_growth ((n' + 1) * (d' + 1) - 1)
  obtain ⟨C₂, hC₂, k₂, h_growth⟩ := multiIndexEquiv_growth d'
  refine ⟨C₂ * C₁ ^ k₂, by positivity, k₁ * k₂, fun m i => ?_⟩
  set α := (multiIndexEquiv ((n' + 1) * (d' + 1) - 1)).symm m
  set β_i := blockMultiIndex (n' + 1) (d' + 1) α i
  have h1 := h_growth β_i
  have h2 : (MultiIndex.abs β_i : ℝ) ≤ MultiIndex.abs α :=
    blockMultiIndex_abs_le (n' + 1) (d' + 1) α i
  have h3 := h_symm m
  calc ((multiIndexEquiv d') β_i : ℝ)
      ≤ C₂ * (1 + (MultiIndex.abs β_i : ℝ)) ^ k₂ - 1 := by linarith
    _ ≤ C₂ * (1 + (MultiIndex.abs α : ℝ)) ^ k₂ := by
        nlinarith [pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + ↑(MultiIndex.abs β_i))
          (show (1 : ℝ) + ↑(MultiIndex.abs β_i) ≤ 1 + ↑(MultiIndex.abs α) by linarith) k₂]
    _ ≤ C₂ * (C₁ * (1 + (m : ℝ)) ^ k₁) ^ k₂ := by gcongr
    _ = C₂ * C₁ ^ k₂ * (1 + (m : ℝ)) ^ (k₁ * k₂) := by rw [mul_pow, ← pow_mul]; ring

/-- **Polynomial growth of `productBasisIndices`.**
Each per-factor basis index grows polynomially in the flat index `m`. -/
theorem productBasisIndices_polyGrowth
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    (n : ℕ) (hn : 0 < n) :
    ∃ C > 0, ∃ q : ℕ, ∀ m i,
      (productBasisIndices (D := D) n hn m i : ℝ) ≤ C * (1 + (m : ℝ)) ^ q := by
  -- Case-split n and d into successors to eliminate Nat.succ_pred casts
  set d := Module.finrank ℝ D
  have hd : 0 < d := Module.finrank_pos
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  obtain ⟨d', hd'⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.succ_pred_eq_of_pos hd).symm⟩
  -- Get the uniform bound from generic_pbi_bound
  obtain ⟨C, hC, q, hbound⟩ := generic_pbi_bound n' d'
  refine ⟨C, hC, q, fun m i => ?_⟩
  -- productBasisIndices (D := D) (n'+1) hn m i unfolds (after rcases) to
  -- multiIndexEquiv d' (Nat.succ_pred ▸ blockMultiIndex (n'+1) (d'+1) (Nat.succ_pred ▸ ...) i)
  -- The Nat.succ_pred casts are trivial when d = d'+1 and n*d = (n'+1)*(d'+1).
  -- We need: productBasisIndices m i = multiIndexEquiv d' (blockMultiIndex ... α i)
  -- This is definitional after subst hd'.
  -- productBasisIndices unfolds to the generic chain when Module.finrank ℝ D = d' + 1.
  -- The `rw` on Module.finrank fails (dependent motive). Use `conv` + `rw` instead.
  -- Blocked by: Module.finrank ℝ D appearing in proof terms inside Nat.succ_pred_eq_of_pos.
  -- The generic bound (generic_pbi_bound) is fully proved above.
  sorry

/-- **Each basis vector of `RapidDecaySeq`, mapped through the product-aware equiv,
gives a product Hermite function.**

The proof traces through the product-aware CLE:
- `(schwartzRapidDecayEquivFin N).symm (basisVec m)` is the multi-dimensional Hermite
  function `∏_J h_{α_J}(e_J)` on `EuclideanSpace ℝ (Fin N)` where `N = n * finrank ℝ D`
- `schwartzDomCongr prodToEuclidean` composes with `prodToEuclidean` which arranges
  Euclidean coordinates in blocks: coordinate `(i,j)` of the flat space corresponds
  to `toEuclidean(x_i)_j`
- The product over all flat coordinates splits as `∏_i ∏_j h_{α_{i,j}}(toEuclidean(x_i)_j)`
- Each inner product `∏_j h_{β_j}(toEuclidean(x_i)_j)` is the DM basis element of `S(D)`
  at the index corresponding to multi-index `β`

As `m` ranges over `ℕ`, the resulting multi-index `α` ranges over all of `Fin N → ℕ`
(via `multiIndexEquiv`), so the per-block multi-indices range independently over all
`Fin (finrank ℝ D) → ℕ`, covering all product Hermite configurations.

The multi-index block decomposition through `prodToEuclidean` and
`multiIndexEquiv` is a concrete Finset.prod regrouping via `finProdFinEquiv`.

The key identity: `∏_{J < N} h_{α_J}(y_J) = ∏_{i < n} ∏_{j < d} h_{α_{(i,j)}}(y_{(i,j)})`
where coordinates are organized in blocks via `finProdFinEquiv`.

This is mathematically just `Finset.prod_equiv finProdFinEquiv` followed by
`Finset.prod_product'` to split the product over `Fin n × Fin d` into iterated
products. The Lean formalization requires carefully tracking the CLE composition
`productRapidDecayEquiv = schwartzDomCongr prodToEuclidean ∘ schwartzRapidDecayEquivFin`
and matching the `multiIndexEquiv` block structure with `blockMultiIndex`.

The proof proceeds in three steps:
A. `equivFin_symm_basisVec` collapses the Hermite series for `basisVec m` to
   `hermiteFunctionNd N α (prodToEuclidean n D x)`.
B. `Finset.prod_equiv finProdFinEquiv` reindexes the flat product over `Fin N` into
   iterated products `∏_i ∏_j` over `Fin n × Fin d`, using the coordinate property
   of `prodToEuclidean`.
C. `cast_equiv_roundtrip` shows that `multiIndexEquiv.symm ∘ multiIndexEquiv` composed
   with the Fin-casts is the identity, matching each block to a DM basis element. -/
theorem productRapidDecayEquiv_symm_basisVec_isProductHermite
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 0 < n) (m : ℕ) :
    ∀ x : Fin n → D,
      ((productRapidDecayEquiv n hn).symm (RapidDecaySeq.basisVec m)).toFun x =
        ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ)
          (productBasisIndices (D := D) n hn m i) (x i) := by
  set d := Module.finrank ℝ D with hd_def
  have hd : 0 < d := Module.finrank_pos
  set N := n * d with hN_def
  have hN : 0 < N := Nat.mul_pos hn hd
  -- The flat multi-index for basisVec m
  have hN1 : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN
  set α : Fin N → ℕ := hN1 ▸ (multiIndexEquiv (N - 1)).symm m with hα_def
  -- Define ks via block decomposition of α
  have hd1 : d - 1 + 1 = d := Nat.succ_pred_eq_of_pos hd
  have hks :
      productBasisIndices (D := D) n hn m =
        (fun i => (multiIndexEquiv (d - 1)) (hd1 ▸ blockMultiIndex n d α i)) := by
    ext i
    simp [productBasisIndices, d, N, α, hd, hN, hd1, hN1]
  intro x
  -- Unfold the product-aware equiv
  -- (productRapidDecayEquiv).symm = (schwartzRapidDecayEquivFin N).symm ∘ schwartzDomCongr prodToEuclidean
  show ((schwartzDomCongr (prodToEuclidean n D))
    ((schwartzRapidDecayEquivFin N hN).symm (RapidDecaySeq.basisVec m))).toFun x = _
  -- schwartzDomCongr composes with prodToEuclidean
  simp only [schwartzDomCongr, ContinuousLinearEquiv.equivOfInverse_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
  -- Step A: LHS = hermiteFunctionNd N α (prodToEuclidean n D x)
  -- compCLMOfContinuousLinearEquiv is composition, so toFun evaluates at prodToEuclidean x.
  -- equivFin_symm_basisVec converts to hermiteFunctionNd via the Hermite series collapse.
  have h_lhs : ((SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (prodToEuclidean n D))
      ((schwartzRapidDecayEquivFin N hN).symm (RapidDecaySeq.basisVec m))).toFun x =
    hermiteFunctionNd N α (prodToEuclidean n D x) :=
    equivFin_symm_basisVec N hN m (prodToEuclidean n D x)
  -- Step B: Split ∏_{J<N} into ∏_{i<n} ∏_{j<d} via finProdFinEquiv, matching blocks.
  have h_blocks : hermiteFunctionNd N α (prodToEuclidean n D x) =
      ∏ i : Fin n, hermiteFunctionNd d (blockMultiIndex n d α i) (toEuclidean (x i)) := by
    simp only [hermiteFunctionNd]
    conv_lhs =>
      rw [show ∏ i_1 : Fin N, hermiteFunction (α i_1) ((prodToEuclidean n D x) i_1) =
        ∏ i_1 : Fin n, ∏ j : Fin d, hermiteFunction (α (finProdFinEquiv (i_1, j)))
          ((prodToEuclidean n D x) (finProdFinEquiv (i_1, j))) from by
        rw [← Finset.prod_product']
        apply Finset.prod_equiv finProdFinEquiv.symm (by simp)
        intro J _; congr 1 <;> exact congrArg _ (finProdFinEquiv.apply_symm_apply J).symm]
    congr 1; ext i
    apply Finset.prod_congr rfl; intro j _
    simp only [blockMultiIndex]
    congr 1
    -- Coordinate property: (prodToEuclidean n D x) (finProdFinEquiv (i,j)) = (toEuclidean (x i)) j
    show (prodToEuclidean n D x) (finProdFinEquiv (i, j)) = (toEuclidean (x i)) j
    simp [prodToEuclidean, flattenEuclidean, curryCLE,
      ContinuousLinearEquiv.piCongrRight, ContinuousLinearEquiv.piCongrLeft,
      EuclideanSpace.equiv, LinearEquiv.curry]; rfl
  -- Step C: Each DM basis element equals hermiteFunctionNd on the corresponding block.
  have h_basis : ∀ i : Fin n,
      DyninMityaginSpace.basis (E := SchwartzMap D ℝ)
        (productBasisIndices (D := D) n hn m i) (x i) =
      hermiteFunctionNd d (blockMultiIndex n d α i) (toEuclidean (x i)) := by
    intro i
    change ((schwartzRapidDecayEquivFin d hd).symm
      (RapidDecaySeq.basisVec (productBasisIndices (D := D) n hn m i))) (toEuclidean (x i)) = _
    rw [equivFin_symm_basisVec]
    show hermiteFunctionNd d (Nat.succ_pred_eq_of_pos hd ▸ (multiIndexEquiv (d - 1)).symm
      (productBasisIndices (D := D) n hn m i)) (toEuclidean (x i)) = _
    rw [hks]
    rw [show (hd1 : d - 1 + 1 = d) = Nat.succ_pred_eq_of_pos hd from rfl]
    rw [cast_equiv_roundtrip d hd (blockMultiIndex n d α i)]
  -- Combine: LHS = ∏ hermiteFunctionNd blocks = RHS
  rw [h_lhs, h_blocks]
  rw [hks]
  congr 1; ext i; exact (h_basis i).symm

/-- Product Hermite functions are dense in Schwartz space on the product domain.

If a continuous linear functional on `S(∏D)` vanishes on all product Hermite functions,
it is zero.

**Proof**: Transfer `φ` to `RapidDecaySeq` via the product-aware CLE
`productRapidDecayEquiv`, which goes through `prodToEuclidean` (applying `toEuclidean`
per component). By `productEquiv_symm_basisVec_isProductHermite`, each basis vector
`basisVec m` maps back to a product Hermite function under the inverse CLE.
The hypothesis `hφ` then gives `(φ ∘ equiv⁻¹)(basisVec m) = 0` for all `m`.
By the `RapidDecaySeq` expansion (`rapidDecay_expansion`), this functional is zero,
hence `φ = 0`.

*Base case* (`n = 1`): Direct transfer via `ContinuousLinearEquiv.funUnique`
reduces to the DM basis of `S(D)`, where `clm_zero_of_basis_zero` applies.

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
    · subst hk
      set T : SchwartzMap D ℝ ≃L[ℝ] SchwartzMap (Fin 1 → D) ℝ :=
        schwartzDomCongr (ContinuousLinearEquiv.funUnique (Fin 1) ℝ D)
      set φ' : SchwartzMap D ℝ →L[ℝ] ℝ := φ.comp T.toContinuousLinearMap
      have h_basis : ∀ m, φ' (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m) = 0 := by
        intro m
        show φ (T (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m)) = 0
        apply hφ (fun _ => m) (T (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m))
        intro x
        simp [T, schwartzDomCongr, SchwartzMap.compCLMOfContinuousLinearEquiv]
      have hφ'_zero : φ' = 0 := clm_zero_of_basis_zero φ' h_basis
      ext f
      have key : φ' (T.symm f) = 0 := by simp [hφ'_zero]
      simp only [φ', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        T.apply_symm_apply] at key
      simpa using key
    · -- case: k ≥ 1, transfer to RapidDecaySeq via product-aware equiv
      have hn' : 0 < k + 1 := by omega
      set equiv := productRapidDecayEquiv (D := D) (k + 1) hn'
      set ψ : RapidDecaySeq →L[ℝ] ℝ := φ.comp equiv.symm.toContinuousLinearMap
      -- Each basisVec maps to a product Hermite, so φ vanishes on it
      have h_vanish : ∀ m, ψ (RapidDecaySeq.basisVec m) = 0 := by
        intro m
        show φ (equiv.symm (RapidDecaySeq.basisVec m)) = 0
        exact hφ (productBasisIndices (D := D) (k + 1) hn' m) _
          (productRapidDecayEquiv_symm_basisVec_isProductHermite (D := D) (k + 1) hn' m)
      -- By the RapidDecaySeq expansion, ψ = 0
      have hψ : ψ = 0 := by
        ext a
        rw [RapidDecaySeq.rapidDecay_expansion ψ a]
        simp [h_vanish]
      -- Transfer back: φ = 0
      ext f
      have : ψ (equiv f) = 0 := by rw [hψ]; simp
      simpa [ψ] using this

end GaussianField
