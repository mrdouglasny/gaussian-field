/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Theorem for Compact Self-Adjoint Operators

Proves the spectral theorem for compact self-adjoint operators on
real Hilbert spaces from 2 axioms:
- `compact_operator_eigenspace_finiteDimensional`
- `compact_selfAdjoint_eigenvalues_finite_above_eps`

Plus 2 proved lemmas:
- `compact_selfAdjoint_hasEigenvector` (proved inline)
- `compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot` (proved inline)

## Main result

`compact_selfAdjoint_spectral`: For any compact self-adjoint T on a real
Hilbert space, there exist a HilbertBasis of eigenvectors and eigenvalues
μ_ι → 0 such that T = ∑ μ_ι ⟨e_ι, ·⟩ e_ι.

## References

- Reed-Simon, "Methods of Modern Mathematical Physics" Vol. 1, Thm VI.11, VI.15, VI.16
- Conway, "A Course in Functional Analysis", Thm II.5.1, II.5.7
- Brezis, "Functional Analysis", Thm 6.11
-/

import GaussianMeasure.Axioms
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Module
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section

namespace GaussianMeasure

open scoped InnerProductSpace
open LinearMap Submodule Filter Metric

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Helper: Eigenvector existence (explicit form)

This helper proves existence of an eigenvector with the explicit form
needed by the eigenspace spanning proof. The eigenvalue is ±‖T‖.
Proof adapted from CompactEigenvector.lean in aqft2. -/

set_option maxHeartbeats 800000 in
private theorem hasEigenvector_aux
    [Nontrivial E]
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ (μ : ℝ) (x : E), x ≠ 0 ∧ (T : E →ₗ[ℝ] E) x = μ • x ∧ |μ| = ‖T‖ := by
  have hα_pos : (0 : ℝ) < ‖T‖ := norm_pos_iff.mpr hne
  have hα_ne : (‖T‖ : ℝ) ≠ 0 := ne_of_gt hα_pos
  have hα2_pos : (0 : ℝ) < ‖T‖ ^ 2 := by positivity
  have hα2_ne : (‖T‖ ^ 2 : ℝ) ≠ 0 := ne_of_gt hα2_pos
  set α := ‖T‖ with hα_def
  have hT_sym : (T : E →ₗ[ℝ] E).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  -- Step 1: Maximizing sequence for ‖Tx‖
  have hseq : ∀ n : ℕ, ∃ x : E, ‖x‖ < 1 ∧ α - 1 / ((n : ℝ) + 1) < ‖T x‖ := by
    intro n
    exact T.exists_lt_apply_of_lt_opNorm (by linarith [show (0:ℝ) < 1/((n:ℝ)+1) from by positivity])
  choose x hx_norm hx_lb using hseq
  -- Step 2: Extract convergent subsequence Tx(φ n) → y
  have hcpt : IsCompact (closure (T '' closedBall (0 : E) 1)) :=
    hK.isCompact_closure_image_closedBall 1
  have hTx_mem : ∀ n, T (x n) ∈ closure (T '' closedBall (0 : E) 1) := by
    intro n
    apply subset_closure
    exact Set.mem_image_of_mem T (mem_closedBall_zero_iff.mpr (hx_norm n).le)
  obtain ⟨y, _, φ, hφ, hTxφ⟩ := hcpt.isSeqCompact hTx_mem
  -- Key: ‖y‖ = α
  have hy_norm : ‖y‖ = α := by
    have hTxφ_norm := (continuous_norm.tendsto y).comp hTxφ
    have hle : ‖y‖ ≤ α := by
      apply le_of_tendsto hTxφ_norm
      apply Filter.Eventually.of_forall; intro n
      calc ‖T (x (φ n))‖ ≤ α * ‖x (φ n)‖ := T.le_opNorm _
        _ ≤ α * 1 := by gcongr; exact (hx_norm _).le
        _ = α := mul_one _
    have hge : α ≤ ‖y‖ := by
      have hf_lb : ∀ n : ℕ, α - 1 / ((n : ℝ) + 1) ≤ ‖T (x (φ n))‖ := by
        intro n
        have h1 := hx_lb (φ n)
        have hφn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hφ.id_le n
        have : 1 / ((φ n : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
        linarith
      have h_lb_tendsto : Tendsto (fun n : ℕ => α - 1 / ((n : ℝ) + 1)) atTop (nhds α) := by
        have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) := by
          have := @tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _
          exact this
        have := tendsto_const_nhds (x := α).sub h1
        simp only [sub_zero] at this; exact this
      have hTxφ_norm' : Tendsto (fun n => ‖T (x (φ n))‖) atTop (nhds ‖y‖) := by
        exact (continuous_norm.tendsto y).comp hTxφ
      exact le_of_tendsto_of_tendsto h_lb_tendsto hTxφ_norm'
        (Filter.Eventually.of_forall hf_lb)
    linarith
  -- Step 3: T(Tx(φ n)) → Ty
  have hTTxφ : Tendsto (fun n => T (T (x (φ n)))) atTop (nhds (T y)) :=
    (T.continuous.tendsto y).comp hTxφ
  -- Step 4: ‖T²x(φ n) - α²·x(φ n)‖ → 0
  have hTx_norm : Tendsto (fun n => ‖T (x (φ n))‖) atTop (nhds α) := by
    rw [← hy_norm]
    exact (continuous_norm.tendsto y).comp hTxφ
  have hkey : Tendsto (fun n => ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖) atTop (nhds 0) := by
    suffices hsq : Tendsto (fun n => ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖ ^ 2) atTop (nhds 0) by
      have := hsq.sqrt
      simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at this
      exact this
    have hpointwise : ∀ n, ‖T (T (x (φ n))) - α ^ 2 • x (φ n)‖ ^ 2 ≤
        α ^ 2 * (α ^ 2 - ‖T (x (φ n))‖ ^ 2) := by
      intro n
      set z := x (φ n)
      have hz_norm : ‖z‖ ≤ 1 := (hx_norm (φ n)).le
      have hTTz_norm : ‖T (T z)‖ ≤ α * ‖T z‖ := T.le_opNorm (T z)
      have hinner : ⟪T (T z), z⟫_ℝ = ‖T z‖ ^ 2 := by
        have h1 : @inner ℝ E _ ((T : E →ₗ[ℝ] E) (T z)) z =
            @inner ℝ E _ (T z) ((T : E →ₗ[ℝ] E) z) := hT_sym (T z) z
        simp only [ContinuousLinearMap.coe_coe] at h1
        rw [h1, real_inner_self_eq_norm_sq]
      have hexpand : ‖T (T z) - α ^ 2 • z‖ ^ 2 =
          ‖T (T z)‖ ^ 2 - 2 * (α ^ 2 * ⟪T (T z), z⟫_ℝ) + (α ^ 2) ^ 2 * ‖z‖ ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right, norm_smul,
            Real.norm_of_nonneg (sq_nonneg α)]
        ring
      rw [hexpand, hinner]
      have h1 : ‖T (T z)‖ ^ 2 ≤ α ^ 2 * ‖T z‖ ^ 2 := by
        calc ‖T (T z)‖ ^ 2 ≤ (α * ‖T z‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) hTTz_norm 2
          _ = α ^ 2 * ‖T z‖ ^ 2 := mul_pow α ‖T z‖ 2
      have h2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - ‖z‖), norm_nonneg z]
      nlinarith
    have h_ub_tendsto : Tendsto (fun n => α ^ 2 * (α ^ 2 - ‖T (x (φ n))‖ ^ 2))
        atTop (nhds 0) := by
      have h1 : Tendsto (fun n => α ^ 2 - ‖T (x (φ n))‖ ^ 2) atTop (nhds 0) := by
        have := tendsto_const_nhds (x := α ^ 2).sub (hTx_norm.pow 2)
        simp only [sub_self] at this; exact this
      have := h1.const_mul (α ^ 2)
      simp only [mul_zero] at this; exact this
    exact squeeze_zero (fun n => sq_nonneg _) hpointwise h_ub_tendsto
  -- Step 5: x(φ n) → Ty/α²
  have hx_conv : Tendsto (fun n => x (φ n)) atTop (nhds ((α ^ 2)⁻¹ • T y)) := by
    have hα2_smul : Tendsto (fun n => α ^ 2 • x (φ n)) atTop (nhds (T y)) := by
      have h_diff : Tendsto (fun n => T (T (x (φ n))) - α ^ 2 • x (φ n)) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        exact hkey
      have : Tendsto (fun n => T (T (x (φ n))) - (T (T (x (φ n))) - α ^ 2 • x (φ n)))
          atTop (nhds (T y - 0)) :=
        hTTxφ.sub h_diff
      simp only [sub_sub_cancel, sub_zero] at this
      exact this
    have hTy_eq : T y = α ^ 2 • ((α ^ 2)⁻¹ • T y) := by
      rw [smul_smul, mul_inv_cancel₀ hα2_ne, one_smul]
    rw [hTy_eq] at hα2_smul
    rwa [tendsto_const_smul_iff₀ hα2_ne] at hα2_smul
  set x₀ := (α ^ 2)⁻¹ • T y with hx₀_def
  -- Step 6: T²x₀ = α²·x₀
  have hT2x0 : T (T x₀) = α ^ 2 • x₀ := by
    have h_TTx0 : T (T x₀) = T y := by
      have h1 : Tendsto (fun n => T (T (x (φ n)))) atTop (nhds (T (T x₀))) :=
        (T.continuous.tendsto (T x₀)).comp ((T.continuous.tendsto x₀).comp hx_conv)
      exact tendsto_nhds_unique h1 hTTxφ
    have h_α2x0 : α ^ 2 • x₀ = T y := by
      simp [hx₀_def, smul_smul, mul_inv_cancel₀ hα2_ne]
    rw [h_TTx0, ← h_α2x0]
  -- Step 7: ‖x₀‖ = 1
  have hx0_norm : ‖x₀‖ = 1 := by
    have hx_norm_conv : Tendsto (fun n => ‖x (φ n)‖) atTop (nhds ‖x₀‖) :=
      (continuous_norm.tendsto x₀).comp hx_conv
    have hge : 1 ≤ ‖x₀‖ := by
      by_contra h
      push_neg at h
      have hlt : α * ‖x₀‖ < α := by nlinarith
      have h_ub : Tendsto (fun n => α * ‖x (φ n)‖) atTop (nhds (α * ‖x₀‖)) :=
        hx_norm_conv.const_mul α
      have h_lb_le : ∀ n, ‖T (x (φ n))‖ ≤ α * ‖x (φ n)‖ := fun n => T.le_opNorm _
      have := le_of_tendsto_of_tendsto hTx_norm h_ub (Filter.Eventually.of_forall h_lb_le)
      linarith
    have hle : ‖x₀‖ ≤ 1 := by
      apply le_of_tendsto hx_norm_conv
      apply Filter.Eventually.of_forall
      intro n; exact (hx_norm _).le
    linarith
  have hx0_ne : x₀ ≠ 0 := by
    intro h; simp [h] at hx0_norm
  -- Step 8: Construct T-eigenvector from T²-eigenvector
  set ep := T x₀ + α • x₀ with hep_def
  set em := T x₀ - α • x₀ with hem_def
  have hTep : T ep = α • ep := by
    simp only [hep_def, map_add, map_smul]
    rw [hT2x0]; module
  have hTem : T em = (-α) • em := by
    simp only [hem_def, map_sub, map_smul]
    rw [hT2x0]; module
  have hne_ep_em : ep ≠ 0 ∨ em ≠ 0 := by
    by_contra h
    push_neg at h
    have : ep - em = ((2 : ℝ) * α) • x₀ := by simp [hep_def, hem_def]; module
    rw [h.1, h.2, sub_zero] at this
    have := smul_eq_zero.mp this.symm
    rcases this with h2 | h2
    · linarith [show (0:ℝ) < 2 * α from by positivity]
    · exact hx0_ne h2
  have hα_abs : |α| = ‖T‖ := abs_of_nonneg (le_of_lt hα_pos)
  rcases hne_ep_em with hep_ne | hem_ne
  · exact ⟨α, ep, hep_ne, by exact_mod_cast hTep, hα_abs⟩
  · exact ⟨-α, em, hem_ne, by exact_mod_cast hTem,
      by rw [abs_neg]; exact hα_abs⟩

/-! ### Theorem 1: Eigenvector existence -/

/-- A compact self-adjoint operator on a nontrivial real Hilbert space
    has an eigenvector achieving ‖T‖. -/
theorem compact_selfAdjoint_hasEigenvector
    [Nontrivial E]
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T)
    (hT_ne : T ≠ 0) :
    ∃ μ : ℝ, Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) μ ∧ |μ| = ‖T‖ := by
  obtain ⟨μ, x, hx_ne, hx_eig, hμ_abs⟩ := hasEigenvector_aux T hT_sa hT_compact hT_ne
  refine ⟨μ, ?_, hμ_abs⟩
  rw [Module.End.HasEigenvalue]
  intro h_bot
  rw [Submodule.eq_bot_iff] at h_bot
  exact hx_ne (h_bot x (Module.End.mem_eigenspace_iff.mpr hx_eig))

/-! ### Theorem 2: Eigenspaces span -/

/-- The orthogonal complement of the span of all eigenspaces is trivial.
    Proved via the "restrict to complement" argument. -/
theorem compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)ᗮ = ⊥ := by
  have hT_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT_sa
  set W := (⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)ᗮ with hW_def
  -- Step 1: T preserves W
  have hW_inv : ∀ w ∈ W, (T : E →ₗ[ℝ] E) w ∈ W :=
    fun w hw => hT_sym.orthogonalComplement_iSup_eigenspaces_invariant hw
  -- Step 2: Build CLM T_W : W →L[ℝ] W
  set T_W := (T.comp W.subtypeL).codRestrict W (fun ⟨u, hu⟩ => hW_inv u hu) with hT_W_def
  -- Step 3: T_W is self-adjoint
  have hT_W_sa : IsSelfAdjoint T_W := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro ⟨x, _⟩ ⟨y, _⟩
    simp only [Submodule.coe_inner]
    change @inner ℝ E _ (T x) y = @inner ℝ E _ x (T y)
    exact hT_sym x y
  -- Step 4: T_W is compact
  have hT_W_compact : IsCompactOperator T_W :=
    (hT_compact.comp_clm W.subtypeL).codRestrict _ (Submodule.isClosed_orthogonal _)
  -- Step 5: T_W = 0
  have hT_W_zero : T_W = 0 := by
    by_contra hT_W_ne
    obtain ⟨v, hv_ne⟩ : ∃ v : ↥W, T_W v ≠ 0 := by
      by_contra h
      push_neg at h
      exact hT_W_ne (ContinuousLinearMap.ext (fun v => h v))
    haveI : Nontrivial W := by
      refine ⟨⟨v, 0, ?_⟩⟩
      intro heq
      exact hv_ne (by rw [heq]; simp)
    obtain ⟨μ, e_W, he_ne, he_eig, _⟩ :=
      hasEigenvector_aux T_W hT_W_sa hT_W_compact hT_W_ne
    have hT_W_sym : (T_W : ↥W →ₗ[ℝ] ↥W).IsSymmetric := by
      rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]; exact hT_W_sa
    have hT_W_eq : (T_W : ↥W →ₗ[ℝ] ↥W) = (T : E →ₗ[ℝ] E).restrict hW_inv := by
      ext ⟨x, hx⟩
      simp only [ContinuousLinearMap.coe_coe, LinearMap.restrict_apply]
      rfl
    have h_no_eig : Module.End.eigenspace ((T : E →ₗ[ℝ] E).restrict hW_inv) μ = ⊥ := by
      have : hW_inv = hT_sym.orthogonalComplement_iSup_eigenspaces_invariant := by
        ext x hx; rfl
      rw [this]
      exact hT_sym.orthogonalComplement_iSup_eigenspaces μ
    have he_mem : e_W ∈ Module.End.eigenspace ((T : E →ₗ[ℝ] E).restrict hW_inv) μ := by
      rw [Module.End.mem_eigenspace_iff]
      rw [← hT_W_eq]
      exact he_eig
    rw [h_no_eig] at he_mem
    exact he_ne ((Submodule.mem_bot ℝ).mp he_mem)
  -- Step 6: W = ⊥
  rw [Submodule.eq_bot_iff]
  intro w hw
  have hTw : (T : E →ₗ[ℝ] E) w = 0 := by
    have : T_W ⟨w, hw⟩ = 0 := by rw [hT_W_zero]; simp
    have h := congr_arg Subtype.val this
    simp only [ZeroMemClass.coe_zero] at h
    exact h
  have hw_eig : w ∈ Module.End.eigenspace (T : E →ₗ[ℝ] E) 0 := by
    rw [Module.End.mem_eigenspace_iff]
    simp [hTw]
  have hw_sup : w ∈ ⨆ μ, Module.End.eigenspace (T : E →ₗ[ℝ] E) μ :=
    le_iSup (fun μ => Module.End.eigenspace (T : E →ₗ[ℝ] E) μ) 0 hw_eig
  have hw_inner : @inner ℝ E _ w w = 0 :=
    Submodule.inner_right_of_mem_orthogonal hw_sup hw
  rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hw_inner

/-! ### Helper: Eigenvector Hilbert basis (Zorn construction) -/

private theorem eigenvector_basis
    (T : E →L[ℝ] E) (hT : IsSelfAdjoint T) (hK : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eigenval : ι → ℝ),
      ∀ i, (T : E →ₗ[ℝ] E) (b i) = eigenval i • b i := by
  have hspan := compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot
    (T := T) hT hK
  have hT_sym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  -- Step 1: Maximal orthonormal subset of eigenvectors via Zorn
  let eigset : Set E := ⋃ (μ : ℝ), ↑(Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)
  have hZ : ∃ S ⊆ eigset, Orthonormal ℝ ((↑) : S → E) ∧
      ∀ u, S ⊆ u → u ⊆ eigset → Orthonormal ℝ ((↑) : u → E) → u = S := by
    have := zorn_subset_nonempty
      {b : Set E | b ⊆ eigset ∧ Orthonormal ℝ ((↑) : b → E)}
      (fun c hc cc _c0 => ⟨⋃₀ c,
        ⟨fun x ⟨s, hs, hx⟩ => (hc hs).1 hx,
         orthonormal_sUnion_of_directed cc.directedOn (fun s hs => (hc hs).2)⟩,
        fun s hs => Set.subset_sUnion_of_mem hs⟩)
      ∅ ⟨Set.empty_subset _, orthonormal_empty ℝ E⟩
    obtain ⟨S, _, hSmax⟩ := this
    have hSe := hSmax.1.1
    have hSo := hSmax.1.2
    exact ⟨S, hSe, hSo, fun u hSu hue huo =>
      (hSmax.2 ⟨hue, huo⟩ hSu).antisymm hSu⟩
  obtain ⟨S, hSe, hSo, hSmax⟩ := hZ
  -- Step 2: T maps span S into itself
  have hT_span_inv : Submodule.span ℝ S ≤ (Submodule.span ℝ S).comap (T : E →ₗ[ℝ] E) := by
    rw [Submodule.span_le]
    intro s hs
    show (T : E →ₗ[ℝ] E) s ∈ Submodule.span ℝ S
    have hse := hSe hs; rw [Set.mem_iUnion] at hse
    obtain ⟨μ, hμ⟩ := hse
    rw [Module.End.mem_eigenspace_iff.mp hμ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hs)
  -- Step 3: T maps (span S)ᗮ into itself
  have hT_orth_inv : ∀ w ∈ (Submodule.span ℝ S)ᗮ,
      (T : E →ₗ[ℝ] E) w ∈ (Submodule.span ℝ S)ᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal'] at hw ⊢
    intro u hu
    rw [real_inner_comm]
    rw [← hT_sym u w, real_inner_comm]
    exact hw _ (hT_span_inv hu)
  -- Step 4: (span ℝ S)ᗮ = ⊥
  have h_span_bot : (Submodule.span ℝ S)ᗮ = ⊥ := by
    by_contra h_ne
    obtain ⟨w, hw, hw_ne⟩ := (Submodule.ne_bot_iff _).mp h_ne
    set W := (Submodule.span ℝ S)ᗮ with hW_def
    have extend_S : ∀ e ∈ W, e ∈ eigset → ‖e‖ = 1 → False := by
      intro e he_W he_eig he_norm
      have he_orth : ∀ s ∈ Submodule.span ℝ S, @inner ℝ E _ e s = 0 := by
        rwa [Submodule.mem_orthogonal'] at he_W
      have he_notin : e ∉ S := by
        intro hmem
        have h_inner := he_orth e (Submodule.subset_span hmem)
        rw [real_inner_self_eq_norm_sq, he_norm, one_pow] at h_inner
        exact one_ne_zero h_inner
      have hSue_orth : Orthonormal ℝ ((↑) : ↥(S ∪ {e}) → E) := by
        refine ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, hx⟩ ⟨y, hy⟩ hne => ?_⟩
        · rcases hx with hx | hx
          · exact hSo.1 ⟨x, hx⟩
          · have := Set.mem_singleton_iff.mp hx; subst this; exact he_norm
        · have hne_val : x ≠ y := fun h => hne (Subtype.ext h)
          rcases hx with hx | hx <;> rcases hy with hy | hy
          · show @inner ℝ E _ x y = 0
            exact hSo.2 (show (⟨x, hx⟩ : ↥S) ≠ ⟨y, hy⟩ from
              fun h => hne_val (congr_arg Subtype.val h))
          · show @inner ℝ E _ x y = 0
            have hye : y = e := Set.mem_singleton_iff.mp hy; subst hye
            rw [real_inner_comm]; exact he_orth x (Submodule.subset_span hx)
          · show @inner ℝ E _ x y = 0
            have hxe : x = e := Set.mem_singleton_iff.mp hx; subst hxe
            exact he_orth y (Submodule.subset_span hy)
          · exfalso; apply hne_val
            rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
      have hSue_sub : S ∪ {e} ⊆ eigset := by
        intro x hx; rcases hx with hx | hx
        · exact hSe hx
        · rw [Set.mem_singleton_iff.mp hx]; exact he_eig
      have hSue_eq := hSmax (S ∪ {e}) Set.subset_union_left hSue_sub hSue_orth
      exact he_notin (hSue_eq ▸ Set.mem_union_right S rfl)
    by_cases hTw_all : ∀ v ∈ W, (T : E →ₗ[ℝ] E) v = 0
    · have hw_norm_ne : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
      exact extend_S ((‖w‖⁻¹ : ℝ) • w) (W.smul_mem _ hw)
        (Set.mem_iUnion.mpr ⟨0, Module.End.mem_eigenspace_iff.mpr (by
          show (T : E →ₗ[ℝ] E) ((‖w‖⁻¹ : ℝ) • w) = 0 • ((‖w‖⁻¹ : ℝ) • w)
          rw [zero_smul, map_smul, hTw_all w hw, smul_zero])⟩)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw_norm_ne])
    · push_neg at hTw_all; obtain ⟨v, hv, hTv_ne⟩ := hTw_all
      set T_W := (T.comp W.subtypeL).codRestrict W (fun ⟨u, hu⟩ => hT_orth_inv u hu)
      have hT_W_sa : IsSelfAdjoint T_W := by
        rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
        intro ⟨x, _⟩ ⟨y, _⟩
        rw [Submodule.coe_inner, Submodule.coe_inner]
        change @inner ℝ E _ (T x) y = @inner ℝ E _ x (T y)
        exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x y
      have hT_W_compact : IsCompactOperator T_W :=
        (hK.comp_clm W.subtypeL).codRestrict _ (Submodule.isClosed_orthogonal _)
      have hT_W_ne : T_W ≠ 0 := by
        intro h
        have : T_W ⟨v, hv⟩ = 0 := by rw [h]; simp
        have h2 : (T_W ⟨v, hv⟩ : E) = 0 := congr_arg Subtype.val this
        exact hTv_ne h2
      haveI : Nontrivial W := by
        refine ⟨⟨⟨v, hv⟩, 0, ?_⟩⟩
        intro h
        have := congr_arg Subtype.val h
        simp only [ZeroMemClass.coe_zero] at this
        exact hTv_ne (by rw [this]; simp)
      obtain ⟨μ, e_W, he_ne, he_eig, _⟩ :=
        hasEigenvector_aux T_W hT_W_sa hT_W_compact hT_W_ne
      have he_eig_E : (T : E →ₗ[ℝ] E) (e_W : E) = μ • (e_W : E) := by
        have h := congr_arg Subtype.val he_eig
        simp only [SetLike.val_smul] at h
        exact h
      have he_norm_ne : ‖(e_W : E)‖ ≠ 0 := by
        intro h; apply he_ne; ext; exact norm_eq_zero.mp h
      exact extend_S ((‖(e_W : E)‖⁻¹ : ℝ) • (e_W : E)) (W.smul_mem _ e_W.2)
        (Set.mem_iUnion.mpr ⟨μ, Module.End.mem_eigenspace_iff.mpr (by
          show (T : E →ₗ[ℝ] E) _ = μ • _
          rw [map_smul, he_eig_E, smul_comm])⟩)
        (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ he_norm_ne])
  -- Step 5: Build HilbertBasis
  have h_range : (Submodule.span ℝ (Set.range ((↑) : S → E)))ᗮ = ⊥ := by
    rwa [Subtype.range_coe_subtype, Set.setOf_mem_eq]
  let b := HilbertBasis.mkOfOrthogonalEqBot hSo h_range
  have h_eig : ∀ (x : S), ∃ μ : ℝ, (T : E →ₗ[ℝ] E) (x : E) = μ • (x : E) := by
    intro ⟨x, hx⟩
    have := hSe hx; rw [Set.mem_iUnion] at this
    obtain ⟨μ, hμ⟩ := this; exact ⟨μ, Module.End.mem_eigenspace_iff.mp hμ⟩
  refine ⟨↥S, b, fun i => (h_eig i).choose, fun i => ?_⟩
  have hbi : (b i : E) = (i : E) :=
    congr_fun (HilbertBasis.coe_mkOfOrthogonalEqBot hSo h_range) i
  rw [hbi]; exact (h_eig i).choose_spec

/-! ### Theorem 3: Spectral theorem (diagonal representation) -/

/-- **Spectral Theorem**: Every compact self-adjoint operator on a real Hilbert
    space admits a HilbertBasis of eigenvectors.

    Given T compact and self-adjoint, there exist:
    - A HilbertBasis {e_ι} (spanning ONB)
    - Eigenvalues μ_ι with T(e_ι) = μ_ι • e_ι
    - Representation: T(x) = ∑_ι μ_ι ⟨e_ι, x⟩ e_ι (norm-convergent) -/
theorem compact_selfAdjoint_spectral
    (T : E →L[ℝ] E)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (ι : Type u) (b : HilbertBasis ι ℝ E) (eigenval : ι → ℝ),
      (∀ i, (T : E →ₗ[ℝ] E) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x)) := by
  obtain ⟨ι, b, μ, hev⟩ := eigenvector_basis T hT_sa hT_compact
  refine ⟨ι, b, μ, hev, fun x => ?_⟩
  have hrepr := b.hasSum_repr x
  have hT_sum : HasSum (fun i => T (b.repr x i • b i)) (T x) :=
    hrepr.mapL T
  have key : ∀ i, T (b.repr x i • b i) = (μ i * @inner ℝ _ _ (b i) x) • b i := fun i => by
    change (T : E →ₗ[ℝ] E) (b.repr x i • b i) = _
    rw [map_smul, hev i, smul_smul, HilbertBasis.repr_apply_apply, mul_comm]
  simp_rw [key] at hT_sum
  exact hT_sum

end GaussianMeasure
