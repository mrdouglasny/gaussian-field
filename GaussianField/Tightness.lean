/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tightness from Uniform Second Moments (Mitoma-Chebyshev)

Proves that a family of probability measures on `Configuration E` with
uniform second moment bounds is tight.

## Main results

- `configuration_tight_of_uniform_second_moments` — the full criterion (0 sorries)

## Key intermediate results

- `DyninMityaginSpace.instBaireSpace` — DM spaces are Baire spaces
  (countable seminorms → pseudometrizable, completeness → Baire)
- `dm_sequentialSpace` — DM spaces are sequential (first countable from
  countably generated uniformity)
- `lowerSemicontinuous_second_moment` — `f ↦ ∫ (ω f)² dμ` is lower
  semicontinuous (sequential Fatou via `lintegral_liminf_le`)
- `uniform_bound_from_pointwise` — Banach-Steinhaus / barrel theorem:
  pointwise bounded second moments → uniform seminorm bound
- `coordBox_isCompact` — compactness of coordinate boxes via sequential
  compactness (Tychonoff + Tannery's theorem + DM reconstruction)
-/

import GaussianField.ConfigurationEmbedding
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Topology.Baire.CompleteMetrizable

noncomputable section

namespace GaussianField

open MeasureTheory Filter Topology
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [hDM : DyninMityaginSpace E]

/-! ## BaireSpace for DyninMityaginSpace -/

/-- A DyninMityaginSpace is a Baire space.

Proof: Countable seminorms → countably generated uniformity → pseudometrizable.
Together with completeness (class field) → completely pseudometrizable → Baire. -/
instance DyninMityaginSpace.instBaireSpace : BaireSpace E := by
  haveI := hDM.h_countable
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : (nhds (0 : E)).IsCountablyGenerated := by
    rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf hDM.p).mp hDM.h_with]
    exact Filter.iInf.isCountablyGenerated _
  haveI : (uniformity E).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  haveI : CompleteSpace E := hDM.h_completeSpace
  infer_instance

/-! ## Uniform bound from pointwise second moments (barrel theorem) -/

private lemma dm_sequentialSpace : SequentialSpace E := by
  haveI := hDM.h_countable
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  haveI : (nhds (0 : E)).IsCountablyGenerated := by
    rw [(SeminormFamily.withSeminorms_iff_nhds_eq_iInf hDM.p).mp hDM.h_with]
    exact Filter.iInf.isCountablyGenerated _
  haveI : (uniformity E).IsCountablyGenerated :=
    IsUniformAddGroup.uniformity_countably_generated
  infer_instance

/-- Each second-moment map `f ↦ ∫ (ω f)² dμ_i` is lower semicontinuous in `f`.

Follows from Fatou's lemma: if `f_n → f`, then `ω(f_n) → ω(f)` for each `ω`
(by continuity of `ω`), so `(ω f_n)² → (ω f)²` pointwise, and Fatou gives
`∫ (ω f)² ≤ liminf ∫ (ω f_n)²`. -/
private lemma lowerSemicontinuous_second_moment
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (h_int : ∀ (f : E) (i : ι),
      Integrable (fun ω : Configuration E => (ω f) ^ 2) (μ i))
    (i : ι) :
    LowerSemicontinuous (fun f : E =>
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i)) := by
  -- Use closed-preimage characterization: LSC ↔ ∀ y, {f | g f ≤ y} is closed
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  -- In a SequentialSpace, closed ↔ sequentially closed
  haveI : SequentialSpace E := dm_sequentialSpace
  rw [← isSeqClosed_iff_isClosed]
  -- Show sequential closedness via Fatou
  intro u f₀ hu_mem hu_tendsto
  -- hu_mem : ∀ n, ∫ (ω (u n))^2 ≤ y
  -- hu_tendsto : u n → f₀
  -- Goal : ∫ (ω f₀)^2 ≤ y
  simp only [Set.mem_preimage, Set.mem_Iic] at hu_mem ⊢
  -- For y < 0: the set is empty since ∫ (ω f)^2 ≥ 0
  by_cases hy : y < 0
  · exact absurd (hu_mem 0) (not_le.mpr (lt_of_lt_of_le hy (integral_nonneg (fun _ => sq_nonneg _))))
  push_neg at hy
  -- Now y ≥ 0
  -- Step 1: Pointwise convergence of (ω (u n))^2 → (ω f₀)^2
  have h_ptwise : ∀ ω' : Configuration E,
      Tendsto (fun n => (ω' (u n)) ^ 2) atTop (nhds ((ω' f₀) ^ 2)) := by
    intro ω'
    exact ((ω'.continuous.continuousAt.tendsto.comp hu_tendsto).pow 2)
  -- Step 2: Fatou via lintegral
  -- Convert Bochner integrals to lintegral via nonneg
  set g := fun (n : ℕ) (ω' : Configuration E) =>
    ENNReal.ofReal ((ω' (u n)) ^ 2) with hg_def
  have h_meas : ∀ n, AEMeasurable (g n) (μ i) := by
    intro n
    exact (h_int (u n) i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  -- lintegral Fatou: ∫⁻ liminf g_n ≤ liminf ∫⁻ g_n
  have h_fatou : ∫⁻ ω', liminf (fun n => g n ω') atTop ∂(μ i) ≤
      liminf (fun n => ∫⁻ ω', g n ω' ∂(μ i)) atTop :=
    lintegral_liminf_le' h_meas
  -- liminf g_n ω' = ENNReal.ofReal ((ω' f₀)^2) (by pointwise convergence)
  have h_liminf_eq : ∀ ω' : Configuration E,
      liminf (fun n => g n ω') atTop = ENNReal.ofReal ((ω' f₀) ^ 2) := by
    intro ω'
    exact (ENNReal.tendsto_ofReal (h_ptwise ω')).liminf_eq
  -- Rewrite LHS of Fatou
  have h_lhs : ∫⁻ ω', ENNReal.ofReal ((ω' f₀) ^ 2) ∂(μ i) ≤
      liminf (fun n => ∫⁻ ω', g n ω' ∂(μ i)) atTop := by
    calc ∫⁻ ω', ENNReal.ofReal ((ω' f₀) ^ 2) ∂(μ i)
        = ∫⁻ ω', liminf (fun n => g n ω') atTop ∂(μ i) := by
          congr 1; ext ω'; exact (h_liminf_eq ω').symm
      _ ≤ liminf (fun n => ∫⁻ ω', g n ω' ∂(μ i)) atTop := h_fatou
  -- Each ∫⁻ g_n = ENNReal.ofReal (∫ (ω (u n))^2) by ofReal_integral_eq_lintegral_ofReal
  have h_rhs_eq : ∀ n, ∫⁻ ω', g n ω' ∂(μ i) =
      ENNReal.ofReal (∫ ω', (ω' (u n)) ^ 2 ∂(μ i)) := by
    intro n
    exact (ofReal_integral_eq_lintegral_ofReal (h_int (u n) i)
      (ae_of_all _ (fun _ => sq_nonneg _))).symm
  -- Similarly for f₀
  have h_lhs_eq : ∫⁻ ω', ENNReal.ofReal ((ω' f₀) ^ 2) ∂(μ i) =
      ENNReal.ofReal (∫ ω', (ω' f₀) ^ 2 ∂(μ i)) := by
    exact (ofReal_integral_eq_lintegral_ofReal (h_int f₀ i)
      (ae_of_all _ (fun _ => sq_nonneg _))).symm
  -- Combine: ENNReal.ofReal (∫ (ω f₀)^2) ≤ liminf ENNReal.ofReal (∫ (ω (u n))^2)
  rw [h_lhs_eq] at h_lhs
  simp_rw [h_rhs_eq] at h_lhs
  -- Each ∫ (ω (u n))^2 ≤ y, so ENNReal.ofReal (∫ ...) ≤ ENNReal.ofReal y
  have h_bound : ∀ n, ENNReal.ofReal (∫ ω', (ω' (u n)) ^ 2 ∂(μ i)) ≤ ENNReal.ofReal y := by
    intro n; exact ENNReal.ofReal_le_ofReal (hu_mem n)
  -- liminf ≤ y
  have h_liminf_le : liminf (fun n => ENNReal.ofReal (∫ ω', (ω' (u n)) ^ 2 ∂(μ i))) atTop ≤
      ENNReal.ofReal y := by
    apply liminf_le_of_le ⟨0, Eventually.of_forall (fun _ => zero_le _)⟩
    intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (h_bound n)
  -- Chain: ENNReal.ofReal (∫ (ω f₀)^2) ≤ ENNReal.ofReal y
  have h_final_ennreal : ENNReal.ofReal (∫ ω', (ω' f₀) ^ 2 ∂(μ i)) ≤ ENNReal.ofReal y :=
    h_lhs.trans h_liminf_le
  -- Since ∫ (ω f₀)^2 ≥ 0 and y ≥ 0, ENNReal.ofReal preserves the order
  exact (ENNReal.ofReal_le_ofReal_iff hy).mp h_final_ennreal

/-- The sublevel set `V_n = {f : E | ∀ i, ∫ (ω f)² dμ_i ≤ n}` is closed.

Each `f ↦ ∫ (ω f)² dμ_i` is lower semicontinuous (by Fatou), so
`{f | ∫ (ω f)² ≤ n}` is closed, and V_n is a countable/arbitrary intersection
of closed sets. -/
private lemma isClosed_sublevel_all
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (h_int : ∀ (f : E) (i : ι),
      Integrable (fun ω : Configuration E => (ω f) ^ 2) (μ i))
    (n : ℕ) :
    IsClosed {f : E | ∀ i, ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ (n : ℝ)} := by
  have h_eq : {f : E | ∀ i, ∫ ω, (ω f) ^ 2 ∂(μ i) ≤ (n : ℝ)} =
      ⋂ i, {f | ∫ ω, (ω f) ^ 2 ∂(μ i) ≤ (n : ℝ)} := by
    ext f; simp [Set.mem_iInter]
  rw [h_eq]
  exact isClosed_iInter (fun i =>
    (lowerSemicontinuous_second_moment μ h_int i).isClosed_preimage _)

omit hDM in
/-- Parallelogram bound for second moments: if `∫(ω(x+cf))² ≤ N` and
`∫(ω(x-cf))² ≤ N`, then `c² * ∫(ωf)² ≤ N`. Uses the identity
`(a+b)²+(a-b)² = 2a²+2b²` and nonnegativity of `∫(ωx)²`. -/
private lemma parallelogram_second_moment_bound
    (μ_i : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (h_int_f : Integrable (fun ω : Configuration E => (ω f) ^ 2) μ_i)
    (h_int_x : Integrable (fun ω : Configuration E => (ω x) ^ 2) μ_i)
    (h_int_xpf : Integrable (fun ω : Configuration E => (ω (x + c • f)) ^ 2) μ_i)
    (h_int_xnf : Integrable (fun ω : Configuration E => (ω (x + (-c) • f)) ^ 2) μ_i)
    (h1 : ∫ ω, (ω (x + c • f)) ^ 2 ∂μ_i ≤ N)
    (h2 : ∫ ω, (ω (x + (-c) • f)) ^ 2 ∂μ_i ≤ N) :
    c ^ 2 * ∫ ω, (ω f) ^ 2 ∂μ_i ≤ N := by
  -- Linearity of ω
  have heq1 : ∀ ω' : Configuration E,
      (ω' (x + c • f)) ^ 2 = (ω' x + c * ω' f) ^ 2 := by
    intro ω'; simp [map_add, map_smul, smul_eq_mul]
  have heq2 : ∀ ω' : Configuration E,
      (ω' (x + (-c) • f)) ^ 2 = (ω' x - c * ω' f) ^ 2 := by
    intro ω'; simp [map_add, map_smul, map_neg, smul_eq_mul]; ring_nf
  -- Parallelogram identity
  have hpara : ∀ ω' : Configuration E,
      (ω' x + c * ω' f) ^ 2 + (ω' x - c * ω' f) ^ 2 =
      2 * (ω' x) ^ 2 + 2 * (c * ω' f) ^ 2 := fun ω' => by ring
  -- Sum bound from h1, h2
  have hsum : ∫ ω', (ω' (x + c • f)) ^ 2 ∂μ_i +
      ∫ ω', (ω' (x + (-c) • f)) ^ 2 ∂μ_i ≤ 2 * N := by linarith
  -- Rewrite sum using linearity
  have h_int_plus : Integrable (fun ω' : Configuration E =>
      (ω' x + c * ω' f) ^ 2) μ_i :=
    h_int_xpf.congr (Eventually.of_forall heq1)
  have h_int_minus : Integrable (fun ω' : Configuration E =>
      (ω' x - c * ω' f) ^ 2) μ_i :=
    h_int_xnf.congr (Eventually.of_forall heq2)
  have hsum_eq :
      ∫ ω', (ω' (x + c • f)) ^ 2 ∂μ_i + ∫ ω', (ω' (x + (-c) • f)) ^ 2 ∂μ_i =
      ∫ ω', ((ω' x + c * ω' f) ^ 2 + (ω' x - c * ω' f) ^ 2) ∂μ_i := by
    conv_lhs =>
      rw [show (fun ω' : Configuration E => (ω' (x + c • f)) ^ 2) =
          (fun ω' => (ω' x + c * ω' f) ^ 2) from funext heq1,
        show (fun ω' : Configuration E => (ω' (x + (-c) • f)) ^ 2) =
          (fun ω' => (ω' x - c * ω' f) ^ 2) from funext heq2]
    exact (integral_add h_int_plus h_int_minus).symm
  -- Apply parallelogram
  have hpara_int :
      ∫ ω', ((ω' x + c * ω' f) ^ 2 + (ω' x - c * ω' f) ^ 2) ∂μ_i =
      ∫ ω', (2 * (ω' x) ^ 2 + 2 * (c * ω' f) ^ 2) ∂μ_i :=
    integral_congr_ae (Eventually.of_forall hpara)
  rw [hsum_eq, hpara_int] at hsum
  -- Split integral
  have h_int_2x : Integrable (fun ω' : Configuration E => 2 * (ω' x) ^ 2) μ_i :=
    h_int_x.const_mul 2
  have h_fn_eq : (fun ω' : Configuration E => 2 * (c * ω' f) ^ 2) =
      (fun ω' => 2 * c ^ 2 * (ω' f) ^ 2) := by ext ω'; ring
  have h_int_2cf : Integrable (fun ω' : Configuration E => 2 * (c * ω' f) ^ 2) μ_i := by
    rw [h_fn_eq]; exact h_int_f.const_mul _
  have hsplit :
      ∫ ω', (2 * (ω' x) ^ 2 + 2 * (c * ω' f) ^ 2) ∂μ_i =
      2 * ∫ ω', (ω' x) ^ 2 ∂μ_i + ∫ ω', 2 * (c * ω' f) ^ 2 ∂μ_i := by
    rw [integral_add h_int_2x h_int_2cf, integral_const_mul]
  rw [hsplit] at hsum
  -- Factor out c² from the second integral
  have hcf_eq : ∫ ω', 2 * (c * ω' f) ^ 2 ∂μ_i =
      2 * c ^ 2 * ∫ ω', (ω' f) ^ 2 ∂μ_i := by
    rw [show (fun ω' : Configuration E => 2 * (c * ω' f) ^ 2) =
        (fun ω' => 2 * c ^ 2 * (ω' f) ^ 2) from by ext ω'; ring,
      integral_const_mul]
  rw [hcf_eq] at hsum
  -- Use nonnegativity of ∫(ωx)²
  have hx_nn : 0 ≤ ∫ ω', (ω' x) ^ 2 ∂μ_i := integral_nonneg fun _ => sq_nonneg _
  linarith

private theorem uniform_bound_from_pointwise
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (_hprob : ∀ i, @IsProbabilityMeasure _ instMeasurableSpaceConfiguration (μ i))
    (h_int : ∀ (f : E) (i : ι),
      Integrable (fun ω : Configuration E => (ω f) ^ 2) (μ i))
    (h_moments : ∀ f : E, ∃ C : ℝ, ∀ i,
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ C) :
    ∃ (s : Finset hDM.ι) (M : ℝ), 0 < M ∧
    ∀ (f : E) (i : ι),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ M * (s.sup hDM.p f) ^ 2 := by
  -- Define sublevel sets V_n = {f : E | ∀ i, ∫ (ω f)² dμ_i ≤ n}
  set V : ℕ → Set E := fun n => {f | ∀ i, ∫ ω, (ω f) ^ 2 ∂(μ i) ≤ (n : ℝ)} with hV_def
  -- Step 1: V_n covers E (by h_moments: pointwise finiteness)
  have h_cover : ⋃ n, V n = Set.univ := by
    ext f; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨C, hC⟩ := h_moments f
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact ⟨n, fun i => (hC i).trans hn⟩
  -- Step 2: Each V_n is closed (lower semicontinuity of second moments)
  have h_closed : ∀ n, IsClosed (V n) := isClosed_sublevel_all μ h_int
  -- Step 3: By Baire category theorem, some V_n has nonempty interior
  haveI : Nonempty E := ⟨0⟩
  obtain ⟨n, x, hx_int⟩ := nonempty_interior_of_iUnion_of_closed h_closed h_cover
  -- x is in V_n
  have hx_Vn : x ∈ V n := interior_subset hx_int
  -- Translate interior point to 0-neighborhood:
  -- {g | x + g ∈ V_n} is a neighborhood of 0
  rw [mem_interior_iff_mem_nhds, ← map_add_left_nhds_zero] at hx_int
  -- Extract from the filter map: {g | x + g ∈ V_n} ∈ nhds 0
  have h_nhds_zero : {g : E | x + g ∈ V n} ∈ 𝓝 (0 : E) := hx_int
  -- By WithSeminorms, extract a finset s and radius r > 0
  rw [hDM.h_with.mem_nhds_iff 0 _] at h_nhds_zero
  obtain ⟨s, r, hr, h_ball_sub⟩ := h_nhds_zero
  -- For f in the ball: x + f ∈ V_n AND x - f ∈ V_n (by symmetry of seminorm balls)
  -- The parallelogram identity gives: (ω f)² = ((ω(x+f))² + (ω(x-f))²)/2 - (ω x)²
  -- So ∫(ω f)² ≤ (∫(ω(x+f))² + ∫(ω(x-f))²)/2 ≤ (n + n)/2 = n
  -- Step 4: For any f with s.sup p f > 0, scale to get the bound
  -- For f with s.sup p f = 0: cf is in ball for all c, so ∫(ω(cf))² ≤ 2n for all c,
  -- hence c²·∫(ω f)² ≤ 2n for all c, so ∫(ω f)² = 0.
  -- Bound: ∀ f i, ∫(ω f)² ≤ M * (s.sup p f)²  where M = 2n / (r/2)²
  refine ⟨s, max 1 (8 * ↑n / r ^ 2), by positivity, fun f i => ?_⟩
  by_cases hf : s.sup hDM.p f = 0
  · -- If s.sup p f = 0, then for all c, s.sup p (c • f) = |c| * 0 = 0 < r
    -- so x + c • f ∈ V_n, meaning ∫(ω(x + c•f))² ≤ n
    -- By parallelogram: c² * ∫(ω f)² ≤ ∫(ω(x+cf))² + ∫(ω(x-cf))² ≤ 2n
    -- For all c, so ∫(ω f)² = 0
    have h_zero : ∫ ω, (ω f) ^ 2 ∂(μ i) = 0 := by
      by_contra h_ne
      push_neg at h_ne
      have h_pos : 0 < ∫ ω, (ω f) ^ 2 ∂(μ i) :=
        lt_of_le_of_ne (integral_nonneg (fun ω => sq_nonneg _)) (Ne.symm h_ne)
      -- Choose c large enough that c² * ∫(ω f)² > 2n
      obtain ⟨c, hc⟩ := exists_nat_gt (2 * ↑n / ∫ ω, (ω f) ^ 2 ∂(μ i))
      have hcf_in_ball : (c : ℝ) • f ∈ (s.sup hDM.p).ball 0 r := by
        simp [Seminorm.mem_ball, sub_zero, map_smul_eq_mul, hf]
        exact hr
      have hcf_Vn : x + (c : ℝ) • f ∈ V n := h_ball_sub hcf_in_ball
      have hncf_Vn : x + (-(c : ℝ) • f) ∈ V n := by
        apply h_ball_sub
        simp [Seminorm.mem_ball, sub_zero, map_smul_eq_mul, map_neg_eq_map, hf]
        exact hr
      -- From membership in V_n:
      have h1 : ∫ ω, (ω (x + (c : ℝ) • f)) ^ 2 ∂(μ i) ≤ n := hcf_Vn i
      have h2 : ∫ ω, (ω (x + (-(c : ℝ) • f))) ^ 2 ∂(μ i) ≤ n := hncf_Vn i
      -- Linearity: ω(x + cf) = ω(x) + c * ω(f)
      -- (ω(x) + c*ω(f))² + (ω(x) - c*ω(f))² = 2*(ω(x))² + 2*(c*ω(f))²
      -- So ∫ 2*(c*ω(f))² ≤ ∫(ω(x+cf))² + ∫(ω(x-cf))² ≤ 2n
      -- i.e., 2*c²*∫(ωf)² ≤ 2n, i.e., c²*∫(ωf)² ≤ n
      have h_eq1 : ∀ ω' : Configuration E,
          (ω' (x + (c : ℝ) • f)) ^ 2 = (ω' x + (c : ℝ) * ω' f) ^ 2 := by
        intro ω'; simp [map_add, map_smul, smul_eq_mul]
      have h_eq2 : ∀ ω' : Configuration E,
          (ω' (x + (-(c : ℝ) • f))) ^ 2 = (ω' x - (c : ℝ) * ω' f) ^ 2 := by
        intro ω'; simp [map_add, map_smul, map_neg, smul_eq_mul]; ring_nf
      -- Use the identity: (a+b)² + (a-b)² = 2a² + 2b²
      have h_para : ∀ ω' : Configuration E,
          (ω' x + (c : ℝ) * ω' f) ^ 2 + (ω' x - (c : ℝ) * ω' f) ^ 2 =
          2 * (ω' x) ^ 2 + 2 * ((c : ℝ) * ω' f) ^ 2 := by
        intro ω'; ring
      -- Integrate both sides
      have h_int_sum :
          ∫ ω', ((ω' x + (c : ℝ) * ω' f) ^ 2 + (ω' x - (c : ℝ) * ω' f) ^ 2) ∂(μ i) =
          ∫ ω', (2 * (ω' x) ^ 2 + 2 * ((c : ℝ) * ω' f) ^ 2) ∂(μ i) :=
        integral_congr_ae (Eventually.of_forall (fun ω' => h_para ω'))
      -- c²·∫(ωf)² ≤ n follows from the parallelogram
      -- We have ∫(ω(x+cf))² + ∫(ω(x-cf))² ≤ 2n
      -- and the LHS equals 2*∫(ωx)² + 2*c²*∫(ωf)² (after splitting integrals)
      -- so 2*c²*∫(ωf)² ≤ 2n (since ∫(ωx)² ≥ 0)
      -- hence c²*∫(ωf)² ≤ n, contradicting c large
      -- Parallelogram: (a+b)²+(a-b)² = 2a²+2b²
      -- So ∫(ω(x+cf))²+∫(ω(x-cf))² = 2∫(ωx)²+2c²∫(ωf)² ≥ 2c²∫(ωf)²
      -- Combined with h1+h2 ≤ 2n gives c²∫(ωf)² ≤ n
      have h_bound_combined :
          (c : ℝ) ^ 2 * ∫ ω', (ω' f) ^ 2 ∂(μ i) ≤ ↑n :=
        parallelogram_second_moment_bound (μ i) (h_int f i) (h_int x i)
          (h_int _ i) (h_int _ i) (hcf_Vn i) (hncf_Vn i)
      -- h_bound_combined: c²·∫(ωf)² ≤ n, hc: 2n/∫(ωf)² < c, h_pos: 0 < ∫(ωf)²
      -- From hc: c·∫(ωf)² > 2n. From h_bound_combined: c²·∫(ωf)² ≤ n.
      -- If c ≥ 1: c²·∫(ωf)² ≥ c·∫(ωf)² > 2n > n, contradiction.
      -- If c = 0: hc says 2n/∫(ωf)² < 0, impossible since n ≥ 0 and ∫(ωf)² > 0.
      have hc_mul := mul_lt_mul_of_pos_right hc h_pos
      rw [div_mul_cancel₀ _ (ne_of_gt h_pos)] at hc_mul
      -- c² * I ≤ n and c * I > 2n. Since I > 0: c > 2n/I ≥ 0, so c ≥ 1.
      -- Then c² * I ≥ c * I > 2n > n, contradiction.
      have hc_ge : (1 : ℝ) ≤ (c : ℝ) := by
        rcases Nat.eq_zero_or_pos c with rfl | hc_pos
        · simp at hc_mul; linarith
        · exact_mod_cast hc_pos
      nlinarith [mul_le_mul_of_nonneg_right hc_ge (le_of_lt h_pos)]
    simp [h_zero]
  · -- General case: s.sup p f > 0, scale f into the ball
    have hf_pos : 0 < s.sup hDM.p f :=
      lt_of_le_of_ne (apply_nonneg _ _) (Ne.symm hf)
    -- Let g = (r/2) / (s.sup p f) • f, then s.sup p g = r/2 < r
    set c := r / 2 / s.sup hDM.p f with hc_def
    have hc_pos : 0 < c := div_pos (by linarith) hf_pos
    have hcf_norm : (s.sup hDM.p) (c • f) = r / 2 := by
      rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos hc_pos, hc_def,
          div_mul_cancel₀ _ (ne_of_gt hf_pos)]
    have hcf_in_ball : c • f ∈ (s.sup hDM.p).ball 0 r := by
      rw [Seminorm.mem_ball, sub_zero, hcf_norm]; linarith
    have hncf_in_ball : (-c) • f ∈ (s.sup hDM.p).ball 0 r := by
      rw [Seminorm.mem_ball, sub_zero, show (-c) • f = -(c • f) from neg_smul c f,
          map_neg_eq_map, hcf_norm]; linarith
    have hxcf_Vn : x + c • f ∈ V n := h_ball_sub hcf_in_ball
    have hxncf_Vn : x + (-c) • f ∈ V n := h_ball_sub hncf_in_ball
    -- Same parallelogram argument as zero case
    have h_cf_bound : c ^ 2 * ∫ ω', (ω' f) ^ 2 ∂(μ i) ≤ ↑n :=
      parallelogram_second_moment_bound (μ i) (h_int f i) (h_int x i)
        (h_int _ i) (h_int _ i) (hxcf_Vn i) (hxncf_Vn i)
    -- So ∫(ωf)² ≤ n / c² = n * (s.sup p f)² / (r/2)² = 4n/(r²) * (s.sup p f)²
    have h_bound : ∫ ω', (ω' f) ^ 2 ∂(μ i) ≤ ↑n / c ^ 2 * (1 : ℝ) := by
      rw [mul_one]
      rw [le_div_iff₀ (sq_pos_of_pos hc_pos)]
      linarith
    -- Simplify: n / c² = n * (s.sup p f)² / (r/2)² = n * (2/r)² * (s.sup p f)²
    calc ∫ ω', (ω' f) ^ 2 ∂(μ i)
        ≤ ↑n / c ^ 2 := by linarith
      _ = 4 * ↑n / r ^ 2 * (s.sup hDM.p f) ^ 2 := by
          rw [hc_def]; field_simp; ring
      _ ≤ (max 1 (8 * ↑n / r ^ 2)) * (s.sup hDM.p f) ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
          apply le_max_of_le_right
          have := Nat.cast_nonneg (α := ℝ) n
          have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
          exact div_le_div_of_nonneg_right (by nlinarith) hr2.le

/-! ## Growth bound on basis moments -/

private theorem basis_moment_poly_bound
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (sd : Finset hDM.ι) (M : ℝ) (hM : 0 < M)
    (h_bound : ∀ (f : E) (i : ι),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ M * (sd.sup hDM.p f) ^ 2) :
    ∃ (B : ℝ) (s : ℕ), 0 < B ∧
    ∀ (m : ℕ) (i : ι),
      ∫ ω : Configuration E, (ω (hDM.basis m)) ^ 2 ∂(μ i) ≤
      B * (1 + (m : ℝ)) ^ (2 * s) := by
  classical
  have hgrowth : ∀ j ∈ sd, ∃ C > 0, ∃ t : ℕ,
      ∀ m, hDM.p j (hDM.basis m) ≤ C * (1 + (m : ℝ)) ^ t :=
    fun j _ => hDM.basis_growth j
  obtain ⟨D, hD, S, hDbound⟩ := finset_sup_poly_bound hDM.p sd hDM.basis hgrowth
  refine ⟨M * D ^ 2, S, by positivity, fun m i => ?_⟩
  calc ∫ ω, (ω (hDM.basis m)) ^ 2 ∂(μ i)
      ≤ M * (sd.sup hDM.p (hDM.basis m)) ^ 2 := h_bound _ i
    _ ≤ M * (D * (1 + (m : ℝ)) ^ S) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hM.le
        apply sq_le_sq'
        · have := apply_nonneg (sd.sup hDM.p) (hDM.basis m)
          have := mul_nonneg hD.le (pow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) S)
          linarith
        · exact hDbound m
    _ = M * D ^ 2 * (1 + (m : ℝ)) ^ (2 * S) := by ring

/-! ## Coordinate box -/

/-- The set of ω with |ω(ψ_m)| ≤ D·(1+m)^r for all m. -/
private def coordBox (D : ℝ) (r : ℕ) : Set (Configuration E) :=
  ⋂ m : ℕ, {ω | |ω (hDM.basis m)| ≤ D * (1 + (m : ℝ)) ^ r}

private theorem coordBox_closed (D : ℝ) (r : ℕ) :
    IsClosed (coordBox (hDM := hDM) D r) := by
  apply isClosed_iInter; intro m
  apply isClosed_le
  · exact continuous_abs.comp (WeakDual.eval_continuous _)
  · exact continuous_const

private theorem coordBox_measurable (D : ℝ) (r : ℕ) :
    @MeasurableSet _ instMeasurableSpaceConfiguration
      (coordBox (hDM := hDM) D r) := by
  apply MeasurableSet.iInter; intro m
  apply measurableSet_le
  · exact (configuration_eval_measurable (hDM.basis m)).norm
  · exact measurable_const

/-- Summability of `|coeff m f| * (1 + m) ^ r` for any `r`, via `coeff_decay`. -/
private lemma summable_coeff_mul_pow (f : E) (r : ℕ) :
    Summable (fun m => |hDM.coeff m f| * (1 + (m : ℝ)) ^ r) := by
  obtain ⟨C_d, hC_d, s_d, hdecay⟩ := hDM.coeff_decay (r + 2)
  apply Summable.of_nonneg_of_le
      (fun m => mul_nonneg (abs_nonneg _) (by positivity))
  · intro m
    calc |hDM.coeff m f| * (1 + (m : ℝ)) ^ r
        = (|hDM.coeff m f| * (1 + (m : ℝ)) ^ (r + 2)) / (1 + (m : ℝ)) ^ 2 := by
          rw [pow_add]; field_simp
      _ ≤ (C_d * (s_d.sup hDM.p) f) / (1 + (m : ℝ)) ^ 2 :=
          div_le_div_of_nonneg_right (hdecay f m) (by positivity)
      _ = C_d * (s_d.sup hDM.p) f * (1 / (1 + (m : ℝ)) ^ 2) := by ring
  · exact ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective |>.congr (fun m => by simp [Nat.succ_eq_add_one]; ring)).mul_left _

/-- Compactness of coordinate boxes via sequential compactness.

Uses: Tychonoff for `ℝ^ℕ` product of intervals, DM expansion + dominated
convergence (Tannery) for weak-* convergence, metrizable space equivalence
`IsCompact ↔ IsSeqCompact`. -/
private theorem coordBox_isCompact
    [PolishSpace (Configuration E)]
    (D : ℝ) (_hD : 0 < D) (r : ℕ) :
    IsCompact (coordBox (hDM := hDM) D r) := by
  -- In a Polish (hence pseudometrizable) space, compact ↔ sequentially compact
  rw [isCompact_iff_isSeqCompact]
  intro ω hω
  -- Step 1: The product box ∏_m Icc(-(D·(1+m)^r), D·(1+m)^r) is compact by Tychonoff
  set B : ℕ → ℝ := fun m => D * (1 + (m : ℝ)) ^ r with hB_def
  set box := Set.pi Set.univ (fun m => Set.Icc (-(B m)) (B m))
  have hbox_compact : IsCompact box := isCompact_univ_pi (fun m => isCompact_Icc)
  -- Step 2: configBasisEval maps coordBox into the product box
  have hω_in_box : ∀ n, configBasisEval (ω n) ∈ box := by
    intro n
    have hωn := hω n
    rw [coordBox, Set.mem_iInter] at hωn
    intro m _
    simp only [configBasisEval, Set.mem_Icc]
    exact ⟨neg_le_of_abs_le (hωn m), le_of_abs_le (hωn m)⟩
  -- Step 3: Extract convergent subsequence in ℝ^ℕ
  obtain ⟨x, hx_mem, φ, hφ_strict, hconv_RN⟩ := hbox_compact.tendsto_subseq hω_in_box
  -- x is in the product box, so |x m| ≤ B m
  have hx_bound : ∀ m, |x m| ≤ B m := by
    intro m; exact abs_le.mpr (hx_mem m (Set.mem_univ m))
  -- configBasisEval (ω (φ n)) → x coordinate-wise
  have hconv_coord : ∀ m, Tendsto (fun n => (ω (φ n)) (hDM.basis m)) atTop (nhds (x m)) := by
    intro m
    have := (continuous_apply m).continuousAt.tendsto.comp hconv_RN
    simpa [Function.comp, configBasisEval] using this
  -- Step 4: Show ω ∘ φ converges pointwise using DM expansion + Tannery
  have hconv_eval : ∀ f : E, Tendsto (fun n => (ω (φ n)) f) atTop
      (nhds (∑' m, hDM.coeff m f * x m)) := by
    intro f
    have h_eq : ∀ n, (ω (φ n)) f = ∑' m, hDM.coeff m f * (ω (φ n)) (hDM.basis m) := by
      intro n; exact hDM.expansion (ω (φ n)) f
    simp_rw [h_eq]
    apply tendsto_tsum_of_dominated_convergence
        (bound := fun m => |hDM.coeff m f| * B m)
    · convert (summable_coeff_mul_pow f r).mul_left D using 1
      ext m
      simp [hB_def]
      ring
    · intro m
      exact (tendsto_const_nhds (x := hDM.coeff m f)).mul (hconv_coord m)
    · apply Eventually.of_forall; intro n m
      rw [Real.norm_eq_abs, abs_mul]
      have hωφn : ω (φ n) ∈ coordBox (hDM := hDM) D r := hω (φ n)
      rw [coordBox, Set.mem_iInter] at hωφn
      exact mul_le_mul_of_nonneg_left (hωφn m) (abs_nonneg _)
  -- Step 5: The limit defines a CLM (continuous linear functional on E)
  have hL_summable : ∀ f : E, Summable (fun m => hDM.coeff m f * x m) := by
    intro f
    apply ((summable_coeff_mul_pow f r).mul_left D).of_norm_bounded_eventually
    apply Eventually.of_forall; intro m
    rw [Real.norm_eq_abs, abs_mul]
    have h : |(hDM.coeff m f)| * |x m| ≤ D * (|(hDM.coeff m f)| * (1 + (m : ℝ)) ^ r) := by
      calc |(hDM.coeff m f)| * |x m|
          ≤ |(hDM.coeff m f)| * (D * (1 + (m : ℝ)) ^ r) := by
            apply mul_le_mul_of_nonneg_left (hx_bound m)
            exact abs_nonneg _
        _ = D * (|(hDM.coeff m f)| * (1 + (m : ℝ)) ^ r) := by ring
    exact h
  -- Define the linear map
  let L_lin : E →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∑' m, hDM.coeff m f * x m
      map_add' := fun f g => by
        show (∑' m, hDM.coeff m (f + g) * x m) =
          (∑' m, hDM.coeff m f * x m) + (∑' m, hDM.coeff m g * x m)
        have h_eq : (fun m => hDM.coeff m (f + g) * x m) =
            (fun m => hDM.coeff m f * x m + hDM.coeff m g * x m) := by
          ext m; rw [map_add]; ring
        rw [h_eq]; exact (hL_summable f).tsum_add (hL_summable g)
      map_smul' := fun c f => by
        show (∑' m, hDM.coeff m (c • f) * x m) = c • (∑' m, hDM.coeff m f * x m)
        have h_eq : (fun m => hDM.coeff m (c • f) * x m) =
            (fun m => c * (hDM.coeff m f * x m)) := by
          ext m; rw [map_smul, smul_eq_mul]; ring
        rw [h_eq, tsum_mul_left, smul_eq_mul] }
  -- Continuity: |L(f)| ≤ C·q(f) for continuous seminorm q, using coeff_decay
  have hL_cont : Continuous L_lin := by
    obtain ⟨C_d, hC_d, s_d, hdecay⟩ := hDM.coeff_decay (r + 2)
    have h_inv_summable : Summable (fun m : ℕ => 1 / (1 + (m : ℝ)) ^ 2) :=
      ((Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
        Nat.succ_injective).congr (fun m => by simp [Nat.succ_eq_add_one]; ring)
    set S' := ∑' (m : ℕ), (1 : ℝ) / (1 + (m : ℝ)) ^ 2
    set q := s_d.sup hDM.p
    have hq_cont : Continuous q :=
      Finset.sup_induction (p := fun (s : Seminorm ℝ E) => Continuous s)
        (show Continuous (⊥ : Seminorm ℝ E) from continuous_const)
        (fun _ ha _ hb => ha.sup hb)
        (fun i _ => hDM.h_with.continuous_seminorm i)
    have hBsum : ∀ f, Summable (fun m => |hDM.coeff m f| * B m) := fun f =>
      ((summable_coeff_mul_pow f r).mul_left D).congr (fun m => by simp [hB_def]; ring)
    have hL_abs_bound : ∀ f, |L_lin f| ≤ D * C_d * S' * q f := by
      intro f
      show |∑' m, hDM.coeff m f * x m| ≤ D * C_d * S' * q f
      have h_abs : |∑' m, hDM.coeff m f * x m| ≤ ∑' m, |hDM.coeff m f| * |x m| := by
        calc |∑' m, hDM.coeff m f * x m|
            ≤ ∑' m, ‖hDM.coeff m f * x m‖ := by
              rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm (hL_summable f).norm
          _ = ∑' m, |hDM.coeff m f| * |x m| := by
              congr 1; ext m; rw [Real.norm_eq_abs, abs_mul]
      have h1 : (∑' m, |hDM.coeff m f| * |x m|) ≤ ∑' m, |hDM.coeff m f| * B m :=
        (((hL_summable f).norm).congr (fun m => by rw [Real.norm_eq_abs, abs_mul])).tsum_le_tsum
          (fun m => mul_le_mul_of_nonneg_left (hx_bound m) (abs_nonneg _)) (hBsum f)
      have h2 : (∑' m, |hDM.coeff m f| * B m) ≤
          ∑' (m : ℕ), C_d * q f * (D / (1 + (m : ℝ)) ^ 2) :=
        (hBsum f).tsum_le_tsum
          (fun m => by
            calc |hDM.coeff m f| * B m
                = (|hDM.coeff m f| * (1 + (m : ℝ)) ^ (r + 2)) * (D / (1 + (m : ℝ)) ^ 2) := by
                  simp only [hB_def]; rw [pow_add]; field_simp
              _ ≤ (C_d * q f) * (D / (1 + (m : ℝ)) ^ 2) :=
                  mul_le_mul_of_nonneg_right (hdecay f m) (by positivity))
          (h_inv_summable.mul_left (C_d * q f * D) |>.congr (fun m => by ring))
      have h3 : (∑' (m : ℕ), C_d * q f * (D / (1 + (m : ℝ)) ^ 2)) =
          D * C_d * S' * q f := by
        conv_lhs => arg 1; ext m; rw [show C_d * q f * (D / (1 + (m : ℝ)) ^ 2) =
          C_d * q f * D * (1 / (1 + (m : ℝ)) ^ 2) from by ring]
        rw [tsum_mul_left]; ring
      linarith
    apply continuous_of_continuousAt_zero L_lin.toAddMonoidHom
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    have hqε : {f : E | q f < ε / (D * C_d * S' + 1)} ∈ nhds (0 : E) :=
      (hq_cont.isOpen_preimage _ isOpen_Iio).mem_nhds (by simp [map_zero]; positivity)
    exact Filter.mem_of_superset hqε (fun f hf => by
      simp only [Real.dist_eq, sub_zero, Set.mem_setOf_eq] at hf ⊢
      have hS'_pos : 0 < S' := by
        have : (∑ m ∈ Finset.range 1, 1 / (1 + (m : ℝ)) ^ 2) ≤ S' :=
          h_inv_summable.sum_le_tsum _ (fun _ _ => by positivity)
        simp at this; linarith
      have hDCS_pos : 0 < D * C_d * S' :=
        mul_pos (mul_pos _hD hC_d) hS'_pos
      calc |L_lin f| ≤ D * C_d * S' * q f := hL_abs_bound f
        _ < D * C_d * S' * (ε / (D * C_d * S' + 1)) :=
            mul_lt_mul_of_pos_left hf hDCS_pos
        _ ≤ (D * C_d * S' + 1) * (ε / (D * C_d * S' + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = ε := mul_div_cancel₀ ε (by positivity))
  -- Package as ContinuousLinearMap = Configuration E
  -- We now build the witness for IsSeqCompact
  refine ⟨⟨L_lin, hL_cont⟩, ?_, φ, hφ_strict, ?_⟩
  · -- Prove ⟨L_lin, hL_cont⟩ ∈ coordBox D r
    rw [coordBox, Set.mem_iInter]; intro m
    simp only [Set.mem_setOf_eq]
    have h_eq : ((⟨L_lin, hL_cont⟩ : Configuration E) : E →L[ℝ] ℝ) (hDM.basis m) = x m :=
      tendsto_nhds_unique (hconv_eval (hDM.basis m)) (hconv_coord m)
    convert hx_bound m using 1
    exact congrArg (fun z => |z|) h_eq
  · -- Prove Tendsto (ω ∘ φ) atTop (nhds ⟨L_lin, hL_cont⟩)
    rw [tendsto_iff_forall_eval_tendsto_topDualPairing]
    intro f; simp only [topDualPairing_apply, Function.comp]
    exact hconv_eval f

/-! ## Chebyshev + union bound -/

private theorem coordBox_compl_mass_le
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (hprob : ∀ i, @IsProbabilityMeasure _ instMeasurableSpaceConfiguration (μ i))
    (B : ℝ) (s : ℕ) (_hB : 0 < B)
    (h_int : ∀ (m : ℕ) (i : ι),
      Integrable[instMeasurableSpaceConfiguration]
      (fun ω : Configuration E => (ω (hDM.basis m)) ^ 2) (μ i))
    (h_bound : ∀ (m : ℕ) (i : ι),
      ∫ ω : Configuration E, (ω (hDM.basis m)) ^ 2 ∂(μ i) ≤
      B * (1 + (m : ℝ)) ^ (2 * s))
    (D : ℝ) (hD : 0 < D) :
    ∀ i, ((μ i) (coordBox (hDM := hDM) D (s + 1))ᶜ).toReal ≤
      B / D ^ 2 * ∑' (m : ℕ), 1 / (1 + (m : ℝ)) ^ 2 := by
  intro i
  haveI := hprob i
  -- Abbreviations
  set R : ℕ → ℝ := fun m => D * (1 + (m : ℝ)) ^ (s + 1) with hR_def
  have hR_pos : ∀ m, 0 < R m := fun m => by positivity
  -- Summability of 1/(1+m)^2
  have h_base_summable : Summable (fun m : ℕ => (1 : ℝ) / (1 + (m : ℝ)) ^ 2) := by
    have h_eq : (fun m : ℕ => (1 : ℝ) / (1 + (m : ℝ)) ^ 2) =
        (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∘ Nat.succ := by
      ext m; simp [Function.comp, Nat.succ_eq_add_one]; ring
    rw [h_eq]
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
  -- Summability of the bound terms B/D^2 * 1/(1+m)^2
  have h_summable : Summable (fun m : ℕ => B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) :=
    h_base_summable.mul_left (B / D ^ 2)
  -- Step 1: coordBox^c ⊆ ⋃ m, {ω | R m < |ω(basis m)|}
  have h_compl_sub : (coordBox (hDM := hDM) D (s + 1))ᶜ ⊆
      ⋃ m, {ω : Configuration E | R m < |ω (hDM.basis m)|} := by
    intro ω hω
    rw [coordBox, Set.mem_compl_iff, Set.mem_iInter, not_forall] at hω
    obtain ⟨m, hm⟩ := hω
    simp only [Set.mem_setOf_eq, not_le] at hm
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  -- Step 2: Bound each term via Chebyshev (Markov applied to f^2)
  have h_term_bound : ∀ m, ((μ i) {ω : Configuration E | R m < |ω (hDM.basis m)|}).toReal ≤
      B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2) := by
    intro m
    have hR2_pos : (0 : ℝ) < (R m) ^ 2 := sq_pos_of_pos (hR_pos m)
    -- {R m < |ω(basis m)|} ⊆ {(R m)^2 ≤ (ω(basis m))^2}
    have h_sub : {ω : Configuration E | R m < |ω (hDM.basis m)|} ⊆
        {ω : Configuration E | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      calc (R m) ^ 2 ≤ |ω (hDM.basis m)| ^ 2 := sq_le_sq' (by linarith [hR_pos m]) hω.le
        _ = (ω (hDM.basis m)) ^ 2 := by rw [sq_abs]
    -- Markov: (R m)^2 * μ.real{(R m)^2 ≤ f^2} ≤ ∫ f^2
    have h_markov : (R m) ^ 2 * (μ i).real
        {ω : Configuration E | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} ≤
        ∫ ω : Configuration E, (ω (hDM.basis m)) ^ 2 ∂(μ i) :=
      mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _)
        (h_int m i) _
    -- Divide by (R m)^2: μ.real{C_m} ≤ B*(1+m)^{2s} / (R m)^2
    have h_div : (μ i).real
        {ω : Configuration E | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} ≤
        B * (1 + (m : ℝ)) ^ (2 * s) / (R m) ^ 2 := by
      rw [le_div_iff₀ hR2_pos]
      calc (μ i).real {ω | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} * (R m) ^ 2
          = (R m) ^ 2 * (μ i).real {ω | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} := mul_comm _ _
        _ ≤ ∫ ω, (ω (hDM.basis m)) ^ 2 ∂(μ i) := h_markov
        _ ≤ B * (1 + (m : ℝ)) ^ (2 * s) := h_bound m i
    -- μ(A_m).toReal ≤ μ(C_m).toReal ≤ B*(1+m)^{2s}/(R m)^2 = B/D^2 * 1/(1+m)^2
    calc ((μ i) {ω | R m < |ω (hDM.basis m)|}).toReal
        ≤ (μ i).real {ω | (R m) ^ 2 ≤ (ω (hDM.basis m)) ^ 2} := by
          unfold Measure.real
          exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono h_sub)
      _ ≤ B * (1 + (m : ℝ)) ^ (2 * s) / (R m) ^ 2 := h_div
      _ = B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2) := by
          rw [hR_def]; field_simp; ring
  -- Step 3: Countable subadditivity: μ(coordBox^c) ≤ Σ' μ(A_m) (ENNReal)
  have h_union_bound : (μ i) (coordBox (hDM := hDM) D (s + 1))ᶜ ≤
      ∑' m, (μ i) {ω : Configuration E | R m < |ω (hDM.basis m)|} :=
    (measure_mono h_compl_sub).trans (measure_iUnion_le _)
  -- The tsum of ENNReal measures is finite (dominated by summable real series)
  have h_tsum_ne_top : (∑' (m : ℕ), (μ i) {ω : Configuration E |
      R m < |ω (hDM.basis m)|}) ≠ ⊤ := by
    -- Each μ(A_m) ≤ ENNReal.ofReal(bound_m), and sum of bounds is finite
    have h_ennreal_bound : ∀ (m : ℕ), (μ i) {ω | R m < |ω (hDM.basis m)|} ≤
        ENNReal.ofReal (B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) := fun m => by
      calc (μ i) {ω | R m < |ω (hDM.basis m)|}
          = ENNReal.ofReal ((μ i) {ω | R m < |ω (hDM.basis m)|}).toReal :=
            (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) :=
            ENNReal.ofReal_le_ofReal (h_term_bound m)
    exact ne_top_of_le_ne_top h_summable.tsum_ofReal_ne_top
      (ENNReal.tsum_le_tsum h_ennreal_bound)
  -- Step 4: Summability of the measure .toReal terms (dominated by the RHS)
  have h_meas_summable : Summable (fun m =>
      ((μ i) {ω : Configuration E | R m < |ω (hDM.basis m)|}).toReal) :=
    Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) h_term_bound h_summable
  -- Step 5: Convert to .toReal and chain inequalities
  have h_le_tsum_real : (∑' (m : ℕ), ((μ i) {ω : Configuration E |
      R m < |ω (hDM.basis m)|}).toReal) ≤
      ∑' (m : ℕ), (B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) :=
    h_meas_summable.tsum_le_tsum h_term_bound h_summable
  have h_tsum_factor : ∑' (m : ℕ), (B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) =
      B / D ^ 2 * ∑' (m : ℕ), 1 / (1 + (m : ℝ)) ^ 2 :=
    tsum_mul_left
  calc ((μ i) (coordBox (hDM := hDM) D (s + 1))ᶜ).toReal
      ≤ (∑' (m : ℕ), (μ i) {ω : Configuration E | R m < |ω (hDM.basis m)|}).toReal :=
        ENNReal.toReal_mono h_tsum_ne_top h_union_bound
    _ = ∑' (m : ℕ), ((μ i) {ω : Configuration E | R m < |ω (hDM.basis m)|}).toReal :=
        ENNReal.tsum_toReal_eq (fun m => measure_ne_top _ _)
    _ ≤ ∑' (m : ℕ), (B / D ^ 2 * (1 / (1 + (m : ℝ)) ^ 2)) := h_le_tsum_real
    _ = B / D ^ 2 * ∑' (m : ℕ), 1 / (1 + (m : ℝ)) ^ 2 := h_tsum_factor

/-! ## Main theorem -/

/-- **Tightness from uniform second moments (Mitoma-Chebyshev).**

On the weak dual of a nuclear Fréchet space, a family of probability
measures with uniformly bounded second moments is tight. -/
theorem configuration_tight_of_uniform_second_moments
    [PolishSpace (Configuration E)] [BorelSpace (Configuration E)]
    {ι : Type*}
    (μ : ι → @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (hprob : ∀ i, @IsProbabilityMeasure _ instMeasurableSpaceConfiguration (μ i))
    (h_int : ∀ (f : E) (i : ι),
      Integrable (fun ω : Configuration E => (ω f) ^ 2) (μ i))
    (h_moments : ∀ f : E, ∃ C : ℝ, ∀ i,
      ∫ ω : Configuration E, (ω f) ^ 2 ∂(μ i) ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : Set (Configuration E),
      IsCompact K ∧ ∀ i, 1 - ε ≤ ((μ i) K).toReal := by
  -- Step 1: Barrel theorem → continuous seminorm bound
  obtain ⟨sd, M, hM, h_bound⟩ := uniform_bound_from_pointwise μ hprob h_int h_moments
  -- Step 2: Polynomial growth of basis moments
  obtain ⟨B, s, hB, h_basis_bound⟩ := basis_moment_poly_bound μ sd M hM h_bound
  -- Step 3: Choose D large enough
  -- Summability: 1/(1+m)^2 = 1/(m+1)^2, summable by p-series with p=2 > 1
  have h_summ : Summable (fun m : ℕ => (1 : ℝ) / (1 + (m : ℝ)) ^ 2) := by
    have h_eq : (fun m : ℕ => (1 : ℝ) / (1 + (m : ℝ)) ^ 2) =
        (fun n : ℕ => 1 / (n : ℝ) ^ 2) ∘ Nat.succ := by
      ext m; simp [Function.comp, Nat.succ_eq_add_one]; ring
    rw [h_eq]
    exact (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
  set S := ∑' (m : ℕ), (1 : ℝ) / (1 + (m : ℝ)) ^ 2
  have hS_pos : 0 < S := by
    have h0 : (0 : ℝ) < 1 / (1 + (0 : ℝ)) ^ 2 := by norm_num
    have h_le : (∑ m ∈ Finset.range 1, 1 / (1 + (m : ℝ)) ^ 2) ≤ S :=
      h_summ.sum_le_tsum _ (fun _ _ => by positivity)
    simp at h_le; linarith
  -- Choose D² ≥ 2·B·S/ε
  set D := Real.sqrt (2 * B * S / ε) with hD_def
  have hD_pos : 0 < D := Real.sqrt_pos_of_pos (by positivity)
  -- Step 4: Define K and show compact + mass bound
  refine ⟨coordBox D (s + 1), coordBox_isCompact D hD_pos (s + 1), fun i => ?_⟩
  -- Integrability from hypothesis
  have h_basis_int : ∀ (m : ℕ) (i' : ι),
      Integrable[instMeasurableSpaceConfiguration]
      (fun ω : Configuration E => (ω (hDM.basis m)) ^ 2) (μ i') :=
    fun m i' => h_int (hDM.basis m) i'
  have h_compl := coordBox_compl_mass_le μ hprob B s hB h_basis_int h_basis_bound D hD_pos i
  have hK_meas := coordBox_measurable (hDM := hDM) D (s + 1)
  -- B/D² * S ≤ ε
  have hD_sq : D ^ 2 = 2 * B * S / ε := by
    rw [sq, hD_def, Real.mul_self_sqrt (by positivity)]
  have h_ratio : B / D ^ 2 * S ≤ ε := by
    rw [hD_sq]
    have hBS_ne : B * S ≠ 0 := ne_of_gt (by positivity)
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have h_eq : B / (2 * B * S / ε) * S = ε / 2 := by field_simp
    linarith [half_le_self hε.le]
  have h_compl_le : ((μ i) (coordBox (hDM := hDM) D (s + 1))ᶜ).toReal ≤ ε :=
    le_trans h_compl h_ratio
  rw [prob_compl_eq_one_sub hK_meas (μ := μ i),
      ENNReal.toReal_sub_of_le
        ((measure_mono (Set.subset_univ _)).trans_eq measure_univ)
        ENNReal.one_ne_top,
      ENNReal.toReal_one] at h_compl_le
  linarith

end GaussianField

end
