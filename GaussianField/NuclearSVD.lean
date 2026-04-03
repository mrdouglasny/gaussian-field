/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear SVD from Spectral Theorem

Given a sequence {y_m} in a separable Hilbert space H with ∑ ‖y_m‖ < ∞,
constructs the singular value decomposition of the associated nuclear
operator A : ℓ² → H, A(e_m) = y_m.

## Main results

- `compact_selfAdjoint_spectral_nat`: ℕ-indexed spectral theorem
- `nuclear_sequence_svd`: SVD for nuclear sequences

## Proof strategy

1. Construct the nuclear operator A : ℓ² → H by A(x) = ∑ xₘ • yₘ
2. Show A is compact (norm limit of finite-rank operators)
3. Apply the spectral theorem to AA† (compact self-adjoint on H)
4. Extract SVD: σₙ = √μₙ, right singular vectors from eigenbasis
5. Verify all required properties
-/

import GaussianField.SpectralTheorem
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Logic.Denumerable
import Mathlib.Topology.Algebra.Module.Basic

open scoped BigOperators
open Filter TopologicalSpace

noncomputable section

namespace GaussianField

/-! ## Section 0: ℓ² basics -/

/-- The ℓ² space used as the domain of the nuclear operator. -/
abbrev ell2' := lp (fun _ : ℕ => ℝ) 2

/-- Standard basis vector in ℓ². -/
def ell2_basis (m : ℕ) : ell2' := lp.single 2 m (1 : ℝ)

/-- The standard basis of ℓ² is orthonormal. -/
theorem ell2_basis_orthonormal : Orthonormal ℝ ell2_basis := by
  refine ⟨fun m => ?_, fun m n hmn => ?_⟩
  · show ‖ell2_basis m‖ = 1
    simp only [ell2_basis]
    have hp : (0 : ENNReal) < 2 := by norm_num
    rw [lp.norm_single hp]
    exact norm_one
  · show @inner ℝ ell2' _ (ell2_basis m) (ell2_basis n) = 0
    simp only [ell2_basis]
    rw [lp.inner_eq_tsum]
    simp only [lp.coeFn_single, Pi.single_apply]
    convert tsum_zero (α := ℝ) (β := ℕ) with i
    simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    split_ifs <;> simp_all

/-- ℓ² is infinite-dimensional. -/
theorem ell2_not_finiteDimensional : ¬ FiniteDimensional ℝ ell2' := by
  intro hfin
  have hli := ell2_basis_orthonormal.linearIndependent
  haveI : Module.Finite ℝ ell2' := hfin
  exact hli.finite.false

/-- ℓ² is separable. -/
instance ell2_separableSpace : SeparableSpace ell2' := by
  rw [← isSeparable_univ_iff]
  have h_dense : (Submodule.span ℝ (Set.range ell2_basis)).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h_sum : HasSum (fun m => lp.single 2 m ((x : ℕ → ℝ) m)) x :=
      lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x
    exact mem_closure_of_tendsto h_sum.tendsto_sum_nat
      (Filter.Eventually.of_forall fun s =>
        Submodule.sum_mem _ fun m _ => by
          have : lp.single 2 m ((x : ℕ → ℝ) m) = (x : ℕ → ℝ) m • ell2_basis m := by
            simp [ell2_basis]; rw [← lp.single_smul]; simp
          rw [this]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩))
  have h1 := (Set.countable_range ell2_basis).isSeparable.span (R := ℝ)
  have h2 := h1.closure
  have h3 : closure (↑(Submodule.span ℝ (Set.range ell2_basis)) : Set ell2') = Set.univ := by
    rw [← Submodule.topologicalClosure_coe, h_dense]; rfl
  rwa [h3] at h2

/-! ## Section 1: ℕ-indexed Spectral Theorem Corollary -/

/-- Orthonormal sets in separable spaces have countable index. -/
theorem orthonormal_countable' {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeparableSpace E] {ι : Type*} {e : ι → E} (he : Orthonormal ℝ e) : Countable ι := by
  apply Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (e i) (1/2))
  · intro i j hij
    rw [Function.onFun, Set.disjoint_left]
    intro z hz1 hz2
    simp only [Metric.mem_ball] at hz1 hz2
    have h_norm : ‖e i - e j‖ ^ 2 = 2 := by
      rw [sq, ← @inner_self_eq_norm_mul_norm ℝ]
      simp only [inner_sub_left, inner_sub_right]
      simp [he.2 hij, he.2 (Ne.symm hij), he.1 i, he.1 j]; ring
    have h_ge : ‖e i - e j‖ ≥ Real.sqrt 2 := by
      by_contra h_lt
      push Not at h_lt
      have := sq_lt_sq' (by linarith [norm_nonneg (e i - e j)]) h_lt
      rw [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)] at this; linarith
    linarith [dist_triangle_left (e i) (e j) z, dist_eq_norm (e i) (e j),
              Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num), Real.sqrt_one]
  · intro i; exact Metric.isOpen_ball
  · intro i; exact ⟨e i, Metric.mem_ball_self (by norm_num)⟩

/-- If a HilbertBasis has finite index, the space is finite-dimensional. -/
theorem hilbertBasis_fintype_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] (b : HilbertBasis ι ℝ E) :
    FiniteDimensional ℝ E := by
  have h_span := b.dense_span
  have h_closed : IsClosed (Submodule.span ℝ (Set.range (b : ι → E)) : Set E) := by
    have : Module.Finite ℝ (Submodule.span ℝ (Set.range (b : ι → E))) :=
      Module.Finite.span_of_finite _ (Set.finite_range _)
    exact Submodule.closed_of_finiteDimensional _
  rw [IsClosed.submodule_topologicalClosure_eq h_closed] at h_span
  have : (⊤ : Submodule ℝ E).FG := by
    rw [← h_span]
    exact ⟨(Set.finite_range (b : ι → E)).toFinset, by rw [Set.Finite.coe_toFinset]⟩
  exact Module.Finite.of_fg_top this

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-- ℕ-indexed corollary of the spectral theorem for compact self-adjoint operators
    on separable infinite-dimensional Hilbert spaces. -/
theorem compact_selfAdjoint_spectral_nat
    (h_inf : ¬ FiniteDimensional ℝ H)
    (T : H →L[ℝ] H)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (u : ℕ → H) (eigenval : ℕ → ℝ),
      Orthonormal ℝ u ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range u)).topologicalClosure) ∧
      (∀ n, (T : H →ₗ[ℝ] H) (u n) = eigenval n • u n) ∧
      (∀ x, HasSum (fun n => (eigenval n * @inner ℝ _ _ (u n) x) • u n) (T x)) := by
  obtain ⟨ι, b, eigenval, hev, hsum⟩ := compact_selfAdjoint_spectral T hT_sa hT_compact
  haveI : Countable ι := orthonormal_countable' b.orthonormal
  haveI : Infinite ι := by
    refine ⟨fun hfin => ?_⟩
    haveI := Fintype.ofFinite ι
    exact h_inf (hilbertBasis_fintype_finiteDimensional b)
  obtain ⟨φ⟩ : Nonempty (ι ≃ ℕ) := nonempty_equiv_of_countable
  refine ⟨b ∘ φ.symm, eigenval ∘ φ.symm, ?_, ?_, ?_, ?_⟩
  · exact b.orthonormal.comp _ φ.symm.injective
  · have h_range : Set.range (b ∘ φ.symm) = Set.range (b : ι → H) := by
      ext x; constructor
      · rintro ⟨n, rfl⟩; exact ⟨φ.symm n, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨φ i, by simp⟩
    rw [h_range]; exact ge_of_eq b.dense_span
  · intro n; exact hev (φ.symm n)
  · intro x; exact (φ.symm.hasSum_iff).mpr (hsum x)

/-! ## Section 2: Nuclear Operator Construction -/

section NuclearOperator

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

omit [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- ∑ ‖yₘ‖ < ∞ implies ∑ ‖yₘ‖² < ∞. -/
theorem summable_norm_sq_of_summable_norm {y : ℕ → K}
    (hy : Summable (fun m => ‖y m‖)) :
    Summable (fun m => ‖y m‖ ^ 2) := by
  apply Summable.of_norm_bounded_eventually_nat hy
  have h_tend := hy.tendsto_atTop_zero
  have h_ev : ∀ᶠ m in atTop, ‖y m‖ < 1 := by
    have := h_tend.eventually (Metric.ball_mem_nhds 0 one_pos)
    exact this.mono fun m hm => by simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hm
  exact h_ev.mono fun m hm => by
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 2)]
    calc ‖y m‖ ^ 2 = ‖y m‖ * ‖y m‖ := sq _
      _ ≤ 1 * ‖y m‖ := mul_le_mul_of_nonneg_right (le_of_lt hm) (norm_nonneg _)
      _ = ‖y m‖ := one_mul _

/-- For x ∈ ℓ² and y with ∑ ‖yₘ‖ < ∞, the series ∑ xₘ • yₘ is summable. -/
theorem summable_smul_of_ell2 (x : ell2') {y : ℕ → K}
    (hy : Summable (fun m => ‖y m‖)) :
    Summable (fun m => (x : ℕ → ℝ) m • y m) := by
  apply Summable.of_norm
  simp_rw [norm_smul]
  have hx_sq : Summable (fun m => ‖(x : ℕ → ℝ) m‖ ^ 2) := by
    refine (lp.summable_inner (𝕜 := ℝ) x x).congr fun m => ?_
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have hy_sq := summable_norm_sq_of_summable_norm hy
  apply Summable.of_nonneg_of_le
    (fun m => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · intro m
    have h_amgm : ‖(x : ℕ → ℝ) m‖ * ‖y m‖ ≤ (‖(x : ℕ → ℝ) m‖ ^ 2 + ‖y m‖ ^ 2) / 2 := by
      have := sq_nonneg (‖(x : ℕ → ℝ) m‖ - ‖y m‖)
      nlinarith [sq_abs (‖(x : ℕ → ℝ) m‖), sq_abs (‖y m‖)]
    exact h_amgm
  · exact (hx_sq.add hy_sq).div_const 2

/-- The linear map underlying the nuclear operator: A(x) = ∑' m, xₘ • yₘ. -/
def nuclear_linearMap (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ell2' →ₗ[ℝ] K where
  toFun x := ∑' m, (x : ℕ → ℝ) m • y m
  map_add' x₁ x₂ := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    have h1 : Summable (fun m => (↑x₁ : ℕ → ℝ) m • y m) := summable_smul_of_ell2 x₁ hy
    have h2 : Summable (fun m => (↑x₂ : ℕ → ℝ) m • y m) := summable_smul_of_ell2 x₂ hy
    exact (h1.hasSum.add h2.hasSum).tsum_eq
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_smul]
    exact (summable_smul_of_ell2 x hy).tsum_const_smul c

/-- Norm bound: ‖A(x)‖ ≤ C ‖x‖. -/
theorem nuclear_operator_bound (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ∃ C : ℝ, ∀ x : ell2', ‖nuclear_linearMap y hy x‖ ≤ C * ‖x‖ := by
  use ∑' m, ‖y m‖
  intro x
  have hp : (2 : ENNReal) ≠ 0 := by norm_num
  have h_bound : ∀ m, ‖(x : ℕ → ℝ) m • y m‖ ≤ ‖x‖ * ‖y m‖ := by
    intro m; rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm hp x m) (norm_nonneg _)
  have h_norm_sum : Summable (fun m => ‖(x : ℕ → ℝ) m • y m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) h_bound (hy.mul_left ‖x‖)
  calc ‖nuclear_linearMap y hy x‖
      ≤ ∑' m, ‖(x : ℕ → ℝ) m • y m‖ := norm_tsum_le_tsum_norm h_norm_sum
    _ ≤ ∑' m, ‖x‖ * ‖y m‖ :=
        Summable.tsum_le_tsum h_bound h_norm_sum (hy.mul_left ‖x‖)
    _ = (∑' m, ‖y m‖) * ‖x‖ := by rw [tsum_mul_left]; ring

/-- The nuclear operator A : ℓ² →L[ℝ] K. -/
def nuclear_clm (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ell2' →L[ℝ] K :=
  (nuclear_linearMap y hy).mkContinuous
    (nuclear_operator_bound y hy).choose
    (nuclear_operator_bound y hy).choose_spec

/-- The nuclear operator maps standard basis vectors to yₘ. -/
theorem nuclear_clm_basis (y : ℕ → K) (hy : Summable (fun m => ‖y m‖))
    (m : ℕ) : nuclear_clm y hy (ell2_basis m) = y m := by
  simp only [nuclear_clm, LinearMap.mkContinuous_apply, nuclear_linearMap,
             LinearMap.coe_mk, AddHom.coe_mk, ell2_basis]
  simp_rw [lp.coeFn_single, Pi.single_apply]
  simp_rw [ite_smul, one_smul, zero_smul]
  rw [tsum_eq_single m (fun k hk => if_neg hk)]
  simp

end NuclearOperator

/-! ## Section 3: Compactness of Nuclear Operators -/

section Compactness

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Inner product with ℓ² basis vector extracts the coordinate. -/
theorem inner_ell2_basis_eq_coord (x : ell2') (m : ℕ) :
    @inner ℝ ell2' _ (ell2_basis m) x = (x : ℕ → ℝ) m := by
  simp only [ell2_basis]
  rw [lp.inner_eq_tsum]
  simp_rw [lp.coeFn_single, Pi.single_apply]
  conv_lhs =>
    arg 1; ext k
    rw [show @inner ℝ ℝ _ (if k = m then (1 : ℝ) else 0) ((x : ℕ → ℝ) k) =
        if k = m then (x : ℕ → ℝ) k else 0 by
      simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      split_ifs <;> simp]
  rw [tsum_eq_single m (fun k hk => if_neg hk)]
  simp

omit [CompleteSpace K] in
/-- Rank-1 operator f.smulRight v is compact. -/
theorem smulRight_isCompactOperator
    (f : ell2' →L[ℝ] ℝ) (v : K) :
    IsCompactOperator (f.smulRight v) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 one_pos, ?_⟩
  refine ⟨(fun c : ℝ => c • v) '' Metric.closedBall 0 ‖f‖, ?_, ?_⟩
  · exact (isCompact_closedBall 0 ‖f‖).image (continuous_id.smul continuous_const)
  · rintro w ⟨x, hx, rfl⟩
    simp only [ContinuousLinearMap.smulRight_apply]
    refine ⟨f x, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hx
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ ‖f‖ * 1 := by apply mul_le_mul_of_nonneg_left (le_of_lt h1) f.opNorm_nonneg
      _ = ‖f‖ := mul_one _

omit [CompleteSpace K] in
/-- Finite sum of compact CLMs is compact. -/
theorem finset_sum_isCompactOperator
    {s : Finset ℕ} {F : ℕ → (ell2' →L[ℝ] K)}
    (hF : ∀ m ∈ s, IsCompactOperator (F m)) :
    IsCompactOperator (∑ m ∈ s, F m) := by
  induction s using Finset.induction with
  | empty => convert isCompactOperator_zero with x
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF _ (Finset.mem_insert_self _ _)).add
      (ih (fun m hm' => hF m (Finset.mem_insert_of_mem hm')))

omit [CompleteSpace K] in
/-- Norm bound for rank-1 CLMs built from ℓ² basis vectors. -/
theorem rank1_norm_le (y : ℕ → K) (m : ℕ) :
    ‖(innerSL ℝ (ell2_basis m)).smulRight (y m)‖ ≤ ‖y m‖ := by
  rw [ContinuousLinearMap.norm_smulRight_apply]
  calc ‖innerSL ℝ (ell2_basis m)‖ * ‖y m‖ ≤ 1 * ‖y m‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [innerSL_apply_norm]
        simp [ell2_basis, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
    _ = ‖y m‖ := one_mul _

/-- Nuclear operators are compact. -/
theorem nuclear_clm_isCompact (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    IsCompactOperator (nuclear_clm y hy) := by
  let T : ℕ → (ell2' →L[ℝ] K) := fun m => (innerSL ℝ (ell2_basis m)).smulRight (y m)
  have hT_summable : Summable T :=
    Summable.of_norm_bounded hy (rank1_norm_le y)
  let A_N : ℕ → (ell2' →L[ℝ] K) := fun N => ∑ m ∈ Finset.range N, T m
  have hA_compact : ∀ N, IsCompactOperator (A_N N) := fun N => by
    show IsCompactOperator ⇑(∑ m ∈ Finset.range N, T m)
    rw [ContinuousLinearMap.coe_sum']
    exact finset_sum_isCompactOperator
      (fun m _ => smulRight_isCompactOperator (innerSL ℝ (ell2_basis m)) (y m))
  have hA_tend_tsum : Tendsto A_N atTop (nhds (∑' m, T m)) :=
    hT_summable.tendsto_sum_tsum_nat
  have hA_eq : ∑' m, T m = nuclear_clm y hy := by
    ext x
    have h_eval : (∑' m, T m) x = ∑' m, (T m) x := by
      change ((ContinuousLinearMap.apply ℝ K) x) (∑' m, T m) =
        ∑' m, ((ContinuousLinearMap.apply ℝ K) x) (T m)
      exact (ContinuousLinearMap.apply ℝ K x).map_tsum hT_summable
    rw [h_eval]
    have h_Tm : ∀ m, (T m) x = (x : ℕ → ℝ) m • y m := by
      intro m
      simp only [T, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
      rw [inner_ell2_basis_eq_coord]
    simp_rw [h_Tm]
    rfl
  rw [hA_eq] at hA_tend_tsum
  exact isCompactOperator_of_tendsto hA_tend_tsum (Filter.Eventually.of_forall hA_compact)

end Compactness

/-! ## Section 4: Gram Operator Properties -/

section GramOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- A†A is self-adjoint. -/
theorem gram_isSelfAdjoint' (T : E →L[ℝ] F) :
    IsSelfAdjoint (T.adjoint.comp T) := by
  rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]

/-- A†A is compact when A is compact. -/
theorem gram_isCompact' (T : E →L[ℝ] F) (hT : IsCompactOperator T) :
    IsCompactOperator (T.adjoint.comp T) :=
  hT.clm_comp T.adjoint

end GramOperator

/-! ## Section 5: Summability of singular values -/

set_option maxHeartbeats 800000 in
/-- Summability of singular values via nuclear norm bound. -/
theorem summable_sqrt_eigenvalues
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (y : ℕ → K) (hy : Summable (fun m => ‖y m‖))
    (A : ell2' →L[ℝ] K) (hA_basis : ∀ m, A (ell2_basis m) = y m)
    (e : ℕ → K) (he_on : Orthonormal ℝ e)
    (μ_ : ℕ → ℝ)
    (h_Bev : ∀ n, (A.comp A.adjoint) (e n) = μ_ n • e n)
    (h_adjnorm : ∀ n, ‖A.adjoint (e n)‖ ^ 2 = μ_ n) :
    Summable (fun n => Real.sqrt (μ_ n)) := by
  have hσ_eq : ∀ n, Real.sqrt (μ_ n) = ‖A.adjoint (e n)‖ := by
    intro n; rw [← Real.sqrt_sq (norm_nonneg _), h_adjnorm]
  have h_adj_orth : ∀ n k, n ≠ k →
      @inner ℝ ell2' _ (A.adjoint (e n)) (A.adjoint (e k)) = 0 := by
    intro n k hnk
    rw [ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e k)]
    conv_lhs => rw [show A (A.adjoint (e n)) = (A.comp A.adjoint) (e n) from
      (ContinuousLinearMap.comp_apply A A.adjoint (e n)).symm]
    rw [h_Bev n, inner_smul_left]; simp [he_on.2 hnk]
  set w : ℕ → ell2' := fun n =>
    if Real.sqrt (μ_ n) = 0 then 0 else (Real.sqrt (μ_ n))⁻¹ • A.adjoint (e n)
  have hw_norm : ∀ n, Real.sqrt (μ_ n) ≠ 0 → ‖w n‖ = 1 := by
    intro n hσ; simp only [w, if_neg hσ, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), hσ_eq, inv_mul_cancel₀]
    rwa [hσ_eq] at hσ
  have hw_orth : ∀ n k, n ≠ k → @inner ℝ ell2' _ (w n) (w k) = 0 := by
    intro n k hnk; simp only [w]
    split_ifs with hn hk hk
    · simp
    · simp
    · simp
    · simp only [inner_smul_left, inner_smul_right, RCLike.conj_to_real,
                  h_adj_orth n k hnk, mul_zero, mul_zero]
  have hw_le : ∀ n, ‖w n‖ ≤ 1 := by
    intro n; by_cases h : Real.sqrt (μ_ n) = 0
    · simp [w, h]
    · exact le_of_eq (hw_norm n h)
  have hw_bessel : ∀ (x : ell2') (S : Finset ℕ),
      ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x S
    set P := ∑ n ∈ S, @inner ℝ ell2' _ (w n) x • w n with hP_def
    have h0 : (0 : ℝ) ≤ ‖x - P‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real] at h0
    have h_xP : @inner ℝ ell2' _ x P = ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 := by
      simp only [hP_def, inner_sum, inner_smul_right, sq, real_inner_comm]
    have h_wP : ∀ n ∈ S, @inner ℝ ell2' _ (w n) P =
        @inner ℝ ell2' _ (w n) x * @inner ℝ ell2' _ (w n) (w n) := by
      intro n hn
      simp only [hP_def, inner_sum, inner_smul_right]
      rw [Finset.sum_eq_single n]
      · intro k _ hkn; rw [hw_orth n k (Ne.symm hkn), mul_zero]
      · intro hn'; exact absurd hn hn'
    have h_P_sq : ‖P‖ ^ 2 ≤ ∑ n ∈ S, (@inner ℝ ell2' _ (w n) x) ^ 2 := by
      rw [hP_def, sq, ← real_inner_self_eq_norm_mul_norm, sum_inner]
      simp only [inner_smul_left, starRingEnd_apply, star_trivial]
      apply Finset.sum_le_sum
      intro n hn
      rw [h_wP n hn, real_inner_self_eq_norm_mul_norm, sq]
      have hw1 : ‖w n‖ * ‖w n‖ ≤ 1 :=
        calc ‖w n‖ * ‖w n‖ ≤ 1 * 1 :=
              mul_le_mul (hw_le n) (hw_le n) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      nlinarith [sq_nonneg (@inner ℝ ell2' _ (w n) x)]
    linarith
  have he_bessel : ∀ (v : K) (S : Finset ℕ),
      ∑ n ∈ S, (@inner ℝ K _ (e n) v) ^ 2 ≤ ‖v‖ ^ 2 := by
    intro v S
    have := he_on.sum_inner_products_le v (s := S)
    simp only [Real.norm_eq_abs, sq_abs] at this; exact this
  apply summable_of_sum_le (c := ∑' m, ‖y m‖) (fun n => Real.sqrt_nonneg _)
  intro S
  have h_coord : ∀ m n, (↑(A.adjoint (e n)) : ℕ → ℝ) m = @inner ℝ K _ (e n) (y m) := by
    intro m n
    have : (↑(A.adjoint (e n)) : ℕ → ℝ) m =
        @inner ℝ ell2' _ (ell2_basis m) (A.adjoint (e n)) := by
      unfold ell2_basis; rw [lp.inner_single_left]
      simp [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    rw [this, ContinuousLinearMap.adjoint_inner_right, hA_basis, real_inner_comm]
  have hc_sum : ∀ n,
      Summable (fun m => (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)) := by
    intro n
    exact (lp.summable_inner (𝕜 := ℝ) (w n) (A.adjoint (e n))).congr
      (fun m => by
        simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, h_coord]; ring)
  have hσ_tsum : ∀ n ∈ S, Real.sqrt (μ_ n) =
      ∑' m, (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m) := by
    intro n _
    by_cases hσ : Real.sqrt (μ_ n) = 0
    · rw [hσ]
      have : w n = 0 := by simp [w, hσ]
      simp only [this, lp.coeFn_zero, Pi.zero_apply, zero_mul, tsum_zero]
    · have hw_eq : w n = (Real.sqrt (μ_ n))⁻¹ • A.adjoint (e n) := by simp [w, hσ]
      have key : @inner ℝ ell2' _ (w n) (A.adjoint (e n)) = Real.sqrt (μ_ n) := by
        rw [hw_eq, inner_smul_left, starRingEnd_apply, star_trivial,
            real_inner_self_eq_norm_mul_norm, ← hσ_eq]; field_simp
      rw [← key, ← (lp.hasSum_inner (𝕜 := ℝ) (w n) (A.adjoint (e n))).tsum_eq]
      congr 1; ext m
      simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real, h_coord]; ring
  calc ∑ n ∈ S, Real.sqrt (μ_ n)
      = ∑ n ∈ S, ∑' m, (↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m) :=
        Finset.sum_congr rfl hσ_tsum
    _ ≤ ∑ n ∈ S, ∑' m, ‖(↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)‖ := by
        apply Finset.sum_le_sum; intro n _
        exact (hc_sum n).tsum_mono (hc_sum n).norm (fun m => Real.le_norm_self _)
    _ = ∑' m, ∑ n ∈ S, ‖(↑(w n) : ℕ → ℝ) m * @inner ℝ K _ (e n) (y m)‖ :=
        (Summable.tsum_finsetSum (fun n _ => (hc_sum n).norm)).symm
    _ ≤ ∑' m, ‖y m‖ := by
        apply (summable_sum (fun n _ => (hc_sum n).norm)).tsum_mono hy
        intro m; simp only [norm_mul, Real.norm_eq_abs]
        calc ∑ n ∈ S, |(↑(w n) : ℕ → ℝ) m| * |@inner ℝ K _ (e n) (y m)|
            ≤ Real.sqrt (∑ n ∈ S, ((↑(w n) : ℕ → ℝ) m) ^ 2) *
              Real.sqrt (∑ n ∈ S, (@inner ℝ K _ (e n) (y m)) ^ 2) := by
              rw [← Real.sqrt_mul (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
              rw [← Real.sqrt_sq (Finset.sum_nonneg
                (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) : (0 : ℝ) ≤ _)]
              apply Real.sqrt_le_sqrt
              have := Finset.sum_mul_sq_le_sq_mul_sq S
                (fun n => |(↑(w n) : ℕ → ℝ) m|) (fun n => |@inner ℝ K _ (e n) (y m)|)
              simp only [sq_abs] at this
              linarith [sq_nonneg (∑ n ∈ S, |(↑(w n) : ℕ → ℝ) m| * |@inner ℝ K _ (e n) (y m)|)]
          _ ≤ 1 * ‖y m‖ := by
              apply mul_le_mul
              · have hw_b := hw_bessel (ell2_basis m) S
                rw [show ‖ell2_basis m‖ = 1 from by
                  simp [ell2_basis, lp.norm_single two_pos], one_pow] at hw_b
                have h_conv : ∀ n, @inner ℝ ell2' _ (w n) (ell2_basis m) =
                    (↑(w n) : ℕ → ℝ) m := by
                  intro n; rw [real_inner_comm]; unfold ell2_basis
                  rw [lp.inner_single_left]
                  simp [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
                simp only [h_conv] at hw_b
                exact (Real.sqrt_le_sqrt hw_b).trans (by rw [Real.sqrt_one])
              · have he_b := he_bessel (y m) S
                exact (Real.sqrt_le_sqrt he_b).trans (by rw [Real.sqrt_sq (norm_nonneg _)])
              · exact Real.sqrt_nonneg _
              · exact le_of_lt zero_lt_one
          _ = ‖y m‖ := one_mul _

/-! ## Section 6: Main Theorem -/

set_option maxHeartbeats 400000 in
/-- **Nuclear sequence SVD — proved from spectral theorem.** -/
theorem nuclear_sequence_svd
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [SeparableSpace K] (h_inf : ¬ FiniteDimensional ℝ K)
    (y : ℕ → K) (hy : Summable (fun m => ‖y m‖)) :
    ∃ (e : ℕ → K) (σ_ : ℕ → ℝ) (W : ℕ → ℕ → ℝ),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      (∀ n, 0 ≤ σ_ n) ∧
      Summable σ_ ∧
      (∀ n m, @inner ℝ K _ (e n) (y m) = σ_ n * W n m) ∧
      (∀ n, σ_ n ≠ 0 → HasSum (fun m => (W n m) ^ 2) 1) ∧
      (∀ n k, n ≠ k → σ_ n ≠ 0 → σ_ k ≠ 0 →
        HasSum (fun m => W n m * W k m) 0) ∧
      (∀ n, σ_ n = 0 → ∀ m, W n m = 0) := by
  -- Step 1: Construct A : ℓ² →L[ℝ] K
  let A := nuclear_clm y hy
  have hA_basis : ∀ m, A (ell2_basis m) = y m := nuclear_clm_basis y hy
  -- Step 2: A is compact
  have hA_compact : IsCompactOperator A := nuclear_clm_isCompact y hy
  -- Step 3: AA† is compact + self-adjoint on K
  set B := A.comp A.adjoint with hB_def
  have hB_sa : IsSelfAdjoint B := by
    rw [IsSelfAdjoint, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
  have hB_compact : IsCompactOperator B := hA_compact.comp_clm A.adjoint
  -- Step 4: Apply spectral theorem to B = AA† on K
  obtain ⟨e, μ_, he_on, he_span, he_ev, he_sum⟩ :=
    compact_selfAdjoint_spectral_nat h_inf B hB_sa hB_compact
  have h_Bev : ∀ n, B (e n) = μ_ n • e n := by
    intro n; exact_mod_cast he_ev n
  -- Helper: ⟨B(eₙ), eₙ⟩ = ‖A†eₙ‖²
  have h_B_inner_adjnorm : ∀ n,
      @inner ℝ K _ (B (e n)) (e n) = ‖A.adjoint (e n)‖ ^ 2 := by
    intro n
    simp only [hB_def, ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e n)]
    exact real_inner_self_eq_norm_sq _
  have h_inner_self_one : ∀ n, @inner ℝ K _ (e n) (e n) = (1 : ℝ) := by
    intro n; rw [real_inner_self_eq_norm_sq, sq, he_on.1 n, mul_one]
  -- Step 5b: Eigenvalues μₙ ≥ 0
  have hμ_nn : ∀ n, 0 ≤ μ_ n := by
    intro n
    have h_eigen : @inner ℝ K _ (B (e n)) (e n) = μ_ n := by
      rw [h_Bev n, real_inner_smul_left, h_inner_self_one, mul_one]
    linarith [h_B_inner_adjnorm n, sq_nonneg ‖A.adjoint (e n)‖]
  have h_adjnorm : ∀ n, ‖A.adjoint (e n)‖ ^ 2 = μ_ n := by
    intro n
    have h2 : @inner ℝ K _ (B (e n)) (e n) = μ_ n := by
      rw [h_Bev n, real_inner_smul_left, h_inner_self_one, mul_one]
    linarith [h_B_inner_adjnorm n]
  -- Step 6: Define σₙ = √μₙ
  let σ_ : ℕ → ℝ := fun n => Real.sqrt (μ_ n)
  have hσ_zero_iff : ∀ n, σ_ n = 0 ↔ μ_ n = 0 := by
    intro n; simp [σ_]; exact Real.sqrt_eq_zero (hμ_nn n)
  have hAdj_zero_of_σ : ∀ n, σ_ n = 0 → A.adjoint (e n) = 0 := by
    intro n hσ
    have hμ : μ_ n = 0 := (hσ_zero_iff n).mp hσ
    have : ‖A.adjoint (e n)‖ ^ 2 = 0 := by rw [h_adjnorm]; exact hμ
    exact norm_eq_zero.mp (by nlinarith [sq_nonneg ‖A.adjoint (e n)‖])
  have h_coord : ∀ n m, @inner ℝ ell2' _ (A.adjoint (e n)) (ell2_basis m) =
      (A.adjoint (e n) : ℕ → ℝ) m :=
    fun n m => by rw [real_inner_comm]; exact inner_ell2_basis_eq_coord _ _
  -- Step 7: Define W
  let W : ℕ → ℕ → ℝ := fun n m =>
    if σ_ n = 0 then 0
    else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m
  -- Step 8: Provide all 8 properties
  refine ⟨e, σ_, W, he_on, he_span, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (3) σₙ ≥ 0
    exact fun n => Real.sqrt_nonneg _
  · -- (4) Summable σ
    exact summable_sqrt_eigenvalues y hy A hA_basis e he_on μ_ h_Bev h_adjnorm
  · -- (5) Inner product formula: ⟨eₙ, yₘ⟩ = σₙ · Wₙₘ
    intro n m
    show @inner ℝ K _ (e n) (y m) =
      σ_ n * (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m)
    split_ifs with hσ
    · have hAdj := hAdj_zero_of_σ n hσ
      rw [← hA_basis m, ← ContinuousLinearMap.adjoint_inner_left, hAdj,
          inner_zero_left]
      simp
    · rw [← hA_basis m, ← ContinuousLinearMap.adjoint_inner_left, h_coord]
      field_simp
  · -- (6) Row orthonormality: σₙ ≠ 0 → HasSum (Wₙₘ²) 1
    intro n hσ_ne
    show HasSum (fun m => (if σ_ n = 0 then 0
      else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) ^ 2) 1
    simp only [if_neg hσ_ne]
    have h := lp.hasSum_inner (𝕜 := ℝ) (A.adjoint (e n)) (A.adjoint (e n))
    rw [real_inner_self_eq_norm_sq] at h
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] at h
    have h2 := h.mul_left ((σ_ n)⁻¹ ^ 2)
    simp only [← mul_pow] at h2
    convert h2 using 1
    rw [mul_pow, inv_pow, h_adjnorm, show σ_ n = Real.sqrt (μ_ n) from rfl,
        Real.sq_sqrt (hμ_nn n)]
    have hμ_ne : μ_ n ≠ 0 := by
      intro h; exact hσ_ne (by simp [σ_, h])
    exact (inv_mul_cancel₀ hμ_ne).symm
  · -- (7) Row orthogonality
    intro n k hnk hσn hσk
    show HasSum (fun m =>
      (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) *
      (if σ_ k = 0 then 0 else (σ_ k)⁻¹ * (A.adjoint (e k) : ℕ → ℝ) m)) 0
    simp only [if_neg hσn, if_neg hσk]
    have h_adj_orth : @inner ℝ ell2' _ (A.adjoint (e n)) (A.adjoint (e k)) = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_right A (A.adjoint (e n)) (e k)]
      conv_lhs => rw [show A (A.adjoint (e n)) = (A.comp A.adjoint) (e n) from
        (ContinuousLinearMap.comp_apply A A.adjoint (e n)).symm]
      rw [h_Bev n, inner_smul_left]
      simp [he_on.2 hnk]
    have h := lp.hasSum_inner (𝕜 := ℝ) (A.adjoint (e n)) (A.adjoint (e k))
    rw [h_adj_orth] at h
    have h2 : HasSum (fun m => (A.adjoint (e n) : ℕ → ℝ) m *
        (A.adjoint (e k) : ℕ → ℝ) m) 0 := by
      convert h using 1; ext m
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]; ring
    have h3 := h2.mul_left ((σ_ n)⁻¹ * (σ_ k)⁻¹)
    simp only [mul_zero] at h3
    convert h3 using 1; ext m; ring
  · -- (8) Zero rows
    intro n hσ m
    show (if σ_ n = 0 then 0 else (σ_ n)⁻¹ * (A.adjoint (e n) : ℕ → ℝ) m) = 0
    simp [hσ]

end GaussianField
