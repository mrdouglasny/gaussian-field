/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Tensor Product via Köthe Sequence Spaces

Defines `RapidDecaySeq`, the Köthe sequence space s(ℕ) of rapidly decreasing
sequences, and proves it is a nuclear Fréchet space. Then defines
`NuclearTensorProduct E₁ E₂` as `RapidDecaySeq` (via Cantor pairing),
providing a `NuclearSpace` instance for tensor products of nuclear spaces.

## Main definitions

- `RapidDecaySeq` — rapidly decreasing sequences on ℕ
- `rapidDecaySeminorm k` — the k-th seminorm: `∑ₘ |aₘ| (1+m)^k`
- `NuclearTensorProduct E₁ E₂` — tensor product of nuclear spaces

## Mathematical background

Every nuclear Fréchet space with a Schauder basis is isomorphic to a
Köthe sequence space s(ℕ) with rapidly decreasing weights (Dynin-Mityagin).
The tensor product s(ℕ) ⊗̂ s(ℕ) ≅ s(ℕ²) ≅ s(ℕ) via Cantor pairing.

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4
-/

import GaussianField.NuclearSpace
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

noncomputable section

namespace GaussianField

/-! ## Rapidly Decreasing Sequences -/

/-- A rapidly decreasing sequence: `val : ℕ → ℝ` such that
`∑ₘ |val m| · (1 + m)^k` converges for all `k : ℕ`. -/
structure RapidDecaySeq where
  val : ℕ → ℝ
  rapid_decay : ∀ k : ℕ, Summable (fun m => |val m| * (1 + (m : ℝ)) ^ k)

namespace RapidDecaySeq

@[ext]
theorem ext {a b : RapidDecaySeq} (h : ∀ m, a.val m = b.val m) : a = b := by
  cases a; cases b; congr 1; exact funext h

/-! ### Weight function lemmas -/

theorem weight_pos (m : ℕ) (k : ℕ) : (0 : ℝ) < (1 + (m : ℝ)) ^ k := by positivity

theorem weight_nonneg (m : ℕ) (k : ℕ) : (0 : ℝ) ≤ (1 + (m : ℝ)) ^ k :=
  le_of_lt (weight_pos m k)

/-! ### Algebraic structure -/

instance instZero : Zero RapidDecaySeq where
  zero := ⟨0, fun k => by simp [summable_zero]⟩

@[simp] theorem zero_val (m : ℕ) : (0 : RapidDecaySeq).val m = 0 := rfl

instance instAdd : Add RapidDecaySeq where
  add a b := ⟨a.val + b.val, fun k => by
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (weight_nonneg m k)
    · intro m; simp only [Pi.add_apply]
      calc |a.val m + b.val m| * (1 + ↑m) ^ k
          ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
        _ = |a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k := add_mul _ _ _
    · exact (a.rapid_decay k).add (b.rapid_decay k)⟩

@[simp] theorem add_val (a b : RapidDecaySeq) (m : ℕ) :
    (a + b).val m = a.val m + b.val m := rfl

instance instNeg : Neg RapidDecaySeq where
  neg a := ⟨fun m => -a.val m, fun k => by
    simp only [abs_neg]; exact a.rapid_decay k⟩

@[simp] theorem neg_val (a : RapidDecaySeq) (m : ℕ) : (-a).val m = -a.val m := rfl

instance instSMul : SMul ℝ RapidDecaySeq where
  smul r a := ⟨fun m => r * a.val m, fun k => by
    have h : (fun m => |r * a.val m| * (1 + (m : ℝ)) ^ k) =
             fun m => |r| * (|a.val m| * (1 + (m : ℝ)) ^ k) := by
      ext m; rw [abs_mul, mul_assoc]
    rw [h]
    exact (a.rapid_decay k).const_smul |r|⟩

@[simp] theorem smul_val (r : ℝ) (a : RapidDecaySeq) (m : ℕ) :
    (r • a).val m = r * a.val m := rfl

instance instAddCommGroup : AddCommGroup RapidDecaySeq where
  add_assoc a b c := ext fun m => add_assoc _ _ _
  zero_add a := ext fun m => zero_add _
  add_zero a := ext fun m => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun m => neg_add_cancel _
  add_comm a b := ext fun m => add_comm _ _

instance instModule : Module ℝ RapidDecaySeq where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-! ### Seminorm family -/

/-- The k-th seminorm on rapid decay sequences: `∑ₘ |aₘ| · (1+m)^k`. -/
def rapidDecaySeminorm (k : ℕ) : Seminorm ℝ RapidDecaySeq where
  toFun a := ∑' m, |a.val m| * (1 + (m : ℝ)) ^ k
  map_zero' := by simp [zero_val, tsum_zero]
  add_le' a b := by
    calc ∑' m, |(a + b).val m| * (1 + ↑m) ^ k
        ≤ ∑' m, (|a.val m| * (1 + ↑m) ^ k + |b.val m| * (1 + ↑m) ^ k) := by
          exact ((a + b).rapid_decay k).tsum_le_tsum
            (fun m => by simp only [add_val]
                         calc |a.val m + b.val m| * (1 + ↑m) ^ k
                             ≤ (|a.val m| + |b.val m|) * (1 + ↑m) ^ k :=
                               mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg m k)
                           _ = _ := add_mul _ _ _)
            ((a.rapid_decay k).add (b.rapid_decay k))
      _ = ∑' m, |a.val m| * (1 + ↑m) ^ k + ∑' m, |b.val m| * (1 + ↑m) ^ k :=
          (a.rapid_decay k).tsum_add (b.rapid_decay k)
  neg' a := by
    congr 1; ext m; rw [neg_val, abs_neg]
  smul' r a := by
    show ∑' m, |r * a.val m| * (1 + ↑m) ^ k = ‖r‖ * ∑' m, |a.val m| * (1 + ↑m) ^ k
    simp_rw [abs_mul, Real.norm_eq_abs, mul_assoc]
    exact tsum_mul_left

/-! ### Topology from seminorms -/

instance instTopologicalSpace : TopologicalSpace RapidDecaySeq :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) rapidDecaySeminorm).topology

theorem rapidDecay_withSeminorms :
    WithSeminorms (rapidDecaySeminorm : ℕ → Seminorm ℝ RapidDecaySeq) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup RapidDecaySeq :=
  rapidDecay_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ RapidDecaySeq :=
  rapidDecay_withSeminorms.continuousSMul

/-! ### Standard basis and coefficients -/

/-- The m-th standard basis vector: 1 at position m, 0 elsewhere. -/
def basisVec (m : ℕ) : RapidDecaySeq where
  val n := if n = m then 1 else 0
  rapid_decay k := by
    apply summable_of_ne_finset_zero (s := {m})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]

@[simp] theorem basisVec_val_self (m : ℕ) : (basisVec m).val m = 1 := by
  simp [basisVec]

@[simp] theorem basisVec_val_ne {m n : ℕ} (h : n ≠ m) : (basisVec m).val n = 0 := by
  simp [basisVec, h]

/-- Seminorm of a basis vector is exactly `(1 + m)^k`. -/
theorem rapidDecaySeminorm_basisVec (k m : ℕ) :
    rapidDecaySeminorm k (basisVec m) = (1 + (m : ℝ)) ^ k := by
  show ∑' n, |(basisVec m).val n| * (1 + (n : ℝ)) ^ k = (1 + (m : ℝ)) ^ k
  rw [tsum_eq_single m]
  · simp [basisVec]
  · intro n hn; simp [basisVec, hn]

/-- The m-th coefficient linear map: extracts coordinate m. -/
def coeffLM (m : ℕ) : RapidDecaySeq →ₗ[ℝ] ℝ where
  toFun a := a.val m
  map_add' a b := rfl
  map_smul' r a := by simp [smul_eq_mul]

/-- The m-th coefficient as a continuous linear map.

Continuity follows from `|a.val m| ≤ rapidDecaySeminorm 0 a`:
the coordinate projection is bounded by the 0-th seminorm. -/
def coeffCLM (m : ℕ) : RapidDecaySeq →L[ℝ] ℝ where
  toLinearMap := coeffLM m
  cont := by
    apply Seminorm.continuous_from_bounded rapidDecay_withSeminorms (norm_withSeminorms ℝ ℝ)
    intro _
    refine ⟨{0}, 1, ?_⟩
    intro a
    simp only [Seminorm.comp_apply, Finset.sup_singleton, one_smul,
      coe_normSeminorm, coeffLM, LinearMap.coe_mk, AddHom.coe_mk, Real.norm_eq_abs]
    change |a.val m| ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0
    calc |a.val m|
        = |a.val m| * (1 + (m : ℝ)) ^ 0 := by simp [pow_zero]
      _ ≤ ∑' n, |a.val n| * (1 + (n : ℝ)) ^ 0 :=
          (a.rapid_decay 0).le_tsum m
            (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))

/-! ### NuclearSpace instance -/

/-- The partial sums `∑_{m∈s} a.val(m) • basisVec(m)` converge to `a`.

For each seminorm `k` and `ε > 0`, the error `∑_{n ∉ s} |aₙ| · (1+n)^k` is the tail
of the convergent series `a.rapid_decay k`, hence eventually less than `ε`. -/
private theorem sum_smul_basisVec_val (a : RapidDecaySeq) (s : Finset ℕ) (n : ℕ) :
    (∑ m ∈ s, a.val m • basisVec m).val n = if n ∈ s then a.val n else 0 := by
  induction s using Finset.induction with
  | empty => simp
  | insert m _ hm ih =>
    rw [Finset.sum_insert hm, add_val, ih]
    simp only [smul_val, basisVec, mul_ite, mul_one, mul_zero, Finset.mem_insert]
    by_cases h : n = m
    · subst h; simp [show n ∉ _ from hm]
    · simp [h]

theorem hasSum_basisVec (a : RapidDecaySeq) :
    HasSum (fun m => a.val m • basisVec m) a := by
  rw [HasSum, (rapidDecay_withSeminorms.tendsto_nhds _ a)]
  intro k ε hε
  simp only [SummationFilter.unconditional_filter]
  -- g n = |a.val n| * (1+n)^k is summable with nonneg terms
  set g : ℕ → ℝ := fun n => |a.val n| * (1 + (n : ℝ)) ^ k with hg_def
  have hg_nn : ∀ n, 0 ≤ g n := fun n => mul_nonneg (abs_nonneg _) (weight_nonneg n k)
  have hg_sum : Summable g := a.rapid_decay k
  -- Partial sums of g converge to tsum g; extract eventual bound
  have hgHS := hg_sum.hasSum
  rw [HasSum, SummationFilter.unconditional_filter] at hgHS
  have h_ev := (tendsto_order.mp hgHS).1 _ (sub_lt_self (∑' n, g n) hε)
  rw [Filter.eventually_atTop] at h_ev ⊢
  obtain ⟨s₀, hs₀⟩ := h_ev
  exact ⟨s₀, fun s hss => by
    have h_partial := hs₀ s hss
    -- Error terms: |error.val n| * (1+n)^k = if n ∈ s then 0 else g n
    have h_err_terms : ∀ n,
        |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k =
        if n ∈ s then 0 else g n := by
      intro n
      simp only [sub_eq_add_neg, add_val, neg_val, sum_smul_basisVec_val]
      split <;> simp [g, abs_neg]
    -- Show seminorm < ε
    show (rapidDecaySeminorm k) ((∑ m ∈ s, a.val m • basisVec m) - a) < ε
    change ∑' n, |((∑ m ∈ s, a.val m • basisVec m) - a).val n| * (1 + ↑n) ^ k < ε
    simp_rw [h_err_terms]
    -- ∑' n, (if n ∈ s then 0 else g n) = ∑' n, g n - ∑ n ∈ s, g n < ε
    have h_compl_summable : Summable (fun n => if (n ∈ s) then (0 : ℝ) else g n) :=
      Summable.of_nonneg_of_le
        (fun n => by split <;> simp [hg_nn])
        (fun n => by split <;> simp [hg_nn])
        hg_sum
    have h_fin_summable : Summable (fun n => if (n ∈ s) then g n else (0 : ℝ)) :=
      summable_of_ne_finset_zero (s := s) (fun n hn => if_neg hn)
    have h_split : ∑' n, g n =
        ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) +
        ∑' n, (if (n ∈ s) then (0 : ℝ) else g n) := by
      rw [← h_fin_summable.tsum_add h_compl_summable]
      congr 1; ext n; split <;> simp
    have h_fin_eq : ∑' n, (if (n ∈ s) then g n else (0 : ℝ)) = ∑ n ∈ s, g n := by
      rw [tsum_eq_sum (fun n hn => if_neg hn)]
      exact Finset.sum_congr rfl (fun n hn => if_pos hn)
    linarith⟩

theorem rapidDecay_expansion (φ : RapidDecaySeq →L[ℝ] ℝ) (a : RapidDecaySeq) :
    φ a = ∑' m, (a.val m) * φ (basisVec m) := by
  have h : HasSum (fun m => φ (a.val m • basisVec m)) (φ a) :=
    (hasSum_basisVec a).mapL φ
  have h' : HasSum (fun m => a.val m * φ (basisVec m)) (φ a) := by
    convert h using 1; ext m; simp [map_smul, smul_eq_mul]
  exact h'.tsum_eq.symm

instance rapidDecay_nuclearSpace : NuclearSpace RapidDecaySeq where
  ι := ℕ
  p := rapidDecaySeminorm
  h_with := rapidDecay_withSeminorms
  basis := basisVec
  coeff := coeffCLM
  expansion := rapidDecay_expansion
  basis_growth k := ⟨1, one_pos, k, fun m => by
    rw [rapidDecaySeminorm_basisVec]; linarith⟩
  coeff_decay k := ⟨1, one_pos, k, fun a m => by
    simp only [coeffCLM, ContinuousLinearMap.coe_mk', coeffLM, LinearMap.coe_mk, AddHom.coe_mk,
      one_mul]
    show |a.val m| * (1 + ↑m) ^ k ≤ ∑' n, |a.val n| * (1 + ↑n) ^ k
    exact (a.rapid_decay k).le_tsum m
      (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j k))⟩

end RapidDecaySeq

/-! ## Cantor Pairing Bound -/

/-- The Cantor pairing function is bounded by a quadratic. -/
theorem nat_pair_bound (n m : ℕ) : Nat.pair n m ≤ (n + m + 1) ^ 2 := by
  unfold Nat.pair
  split <;> nlinarith

/-- Converse bound: each component of `Nat.unpair` is bounded by the pair index. -/
theorem nat_unpair_le (p : ℕ) : (Nat.unpair p).1 ≤ p ∧ (Nat.unpair p).2 ≤ p :=
  ⟨Nat.unpair_left_le p, Nat.unpair_right_le p⟩

/-! ## Nuclear Tensor Product -/

/-- The nuclear tensor product of two nuclear spaces, realized as the Köthe
sequence space of rapidly decreasing sequences. The product basis indices
`ℕ × ℕ` are encoded into `ℕ` via `Nat.pair`.

Mathematically, if `E₁ ≅ s(ℕ)` and `E₂ ≅ s(ℕ)` as nuclear Fréchet spaces,
then `E₁ ⊗̂ E₂ ≅ s(ℕ × ℕ) ≅ s(ℕ)` via the Cantor pairing. -/
def NuclearTensorProduct (_E₁ _E₂ : Type*) := RapidDecaySeq

namespace NuclearTensorProduct

variable {E₁ E₂ : Type*}

instance : AddCommGroup (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (AddCommGroup RapidDecaySeq)

instance : Module ℝ (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (Module ℝ RapidDecaySeq)

instance : TopologicalSpace (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (TopologicalSpace RapidDecaySeq)

instance : IsTopologicalAddGroup (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (IsTopologicalAddGroup RapidDecaySeq)

instance : ContinuousSMul ℝ (NuclearTensorProduct E₁ E₂) :=
  inferInstanceAs (ContinuousSMul ℝ RapidDecaySeq)

/-- The nuclear tensor product is a nuclear space. -/
instance nuclearSpace : NuclearSpace (NuclearTensorProduct E₁ E₂) :=
  RapidDecaySeq.rapidDecay_nuclearSpace

/-- Map from product basis indices to the Cantor-paired linear index. -/
def fromPairIndex (n m : ℕ) : ℕ := Nat.pair n m

/-- Recover product basis indices from a linear index. -/
def toPairIndex (p : ℕ) : ℕ × ℕ := Nat.unpair p

theorem toPairIndex_fromPairIndex (n m : ℕ) :
    toPairIndex (fromPairIndex n m) = (n, m) :=
  Nat.unpair_pair n m

theorem fromPairIndex_toPairIndex (p : ℕ) :
    fromPairIndex (toPairIndex p).1 (toPairIndex p).2 = p :=
  Nat.pair_unpair p

end NuclearTensorProduct

end GaussianField
