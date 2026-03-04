/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Measure Support Theorem

Characterizes the support of the Gaussian measure μ_T on the weak dual E'.
The measure is supported on configurations with finite Cameron-Martin norm
(i.e., Σₙ |ω(eₙ)|² < ∞) if and only if T is Hilbert-Schmidt with respect
to the DyninMityaginSpace basis.

## Main definitions

- `IsHilbertSchmidt T` — T is Hilbert-Schmidt: Σₙ ‖T(eₙ)‖² < ∞
- `hilbertSchmidtNormSq T` — the HS norm squared: Σₙ ‖T(eₙ)‖²
- `cameronMartinInner T` — the Cameron-Martin inner product C(f,g)
- `cameronMartinNormSq T` — the Cameron-Martin norm squared ‖T(f)‖²

## Main results

- `expected_norm_sq_eq_hs` — E[Σₙ |ω(eₙ)|²] = Σₙ ‖T(eₙ)‖² (HS norm²)
- `support_of_hilbertSchmidt` — if T is HS, then a.e. ω has Σₙ |ω(eₙ)|² < ∞
- `not_supported_of_not_hilbertSchmidt` — converse: not HS ⟹ a.s. divergent
- `gaussian_support_iff` — the iff characterization

## References

- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*, Ch. 1
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Ch. II
-/

import GaussianField.Properties
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal
open Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-! ## Cameron-Martin inner product and norm -/

/-- The Cameron-Martin inner product: ⟨f, g⟩₀ = ⟨T(f), T(g)⟩_H = C(f,g).
    This is the reproducing kernel inner product of the Gaussian measure. -/
def cameronMartinInner (T : E →L[ℝ] H) (f g : E) : ℝ :=
  covariance T f g

/-- The Cameron-Martin norm squared: ‖f‖₀² = ‖T(f)‖²_H.
    The Cameron-Martin space H₀ is the completion of E under this norm. -/
def cameronMartinNormSq (T : E →L[ℝ] H) (f : E) : ℝ :=
  ‖T f‖ ^ 2

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
  [CompleteSpace H] [SeparableSpace H] in
theorem cameronMartinNormSq_eq_inner (T : E →L[ℝ] H) (f : E) :
    cameronMartinNormSq T f = cameronMartinInner T f f := by
  simp [cameronMartinNormSq, cameronMartinInner, covariance]

/-! ## Hilbert-Schmidt condition -/

/-- T is Hilbert-Schmidt with respect to the DyninMityaginSpace basis:
    Σₙ ‖T(eₙ)‖² < ∞, where (eₙ) is the Schauder basis of E.

    In the QFT application, this is the condition for the Gaussian measure
    to be supported on a Sobolev space rather than the full distributional dual. -/
def IsHilbertSchmidt (T : E →L[ℝ] H) : Prop :=
  Summable (fun n => ‖T (DyninMityaginSpace.basis n)‖ ^ 2)

/-- The Hilbert-Schmidt norm squared: Σₙ ‖T(eₙ)‖².
    This equals the expected squared norm E[Σₙ |ω(eₙ)|²] of the field. -/
noncomputable def hilbertSchmidtNormSq (T : E →L[ℝ] H) : ℝ :=
  ∑' n, ‖T (DyninMityaginSpace.basis n)‖ ^ 2

/-- The squared norm of ω in the basis: Σₙ |ω(eₙ)|². -/
noncomputable def basisNormSq (ω : Configuration E) : ℝ :=
  ∑' n, (ω (DyninMityaginSpace.basis n)) ^ 2

/-! ## Expected squared norm equals HS norm -/

/-- Each term E[|ω(eₙ)|²] = ‖T(eₙ)‖² is the second moment identity
    applied to the n-th basis element. -/
theorem basis_second_moment (T : E →L[ℝ] H) (n : ℕ) :
    ∫ ω : Configuration E, (ω (DyninMityaginSpace.basis n)) ^ 2 ∂(measure T) =
      ‖T (DyninMityaginSpace.basis n)‖ ^ 2 := by
  rw [second_moment_eq_covariance]
  exact real_inner_self_eq_norm_sq (T (DyninMityaginSpace.basis n))

/-- Each basis pairing squared is integrable. -/
theorem basis_sq_integrable (T : E →L[ℝ] H) (n : ℕ) :
    Integrable (fun ω : Configuration E =>
      (ω (DyninMityaginSpace.basis n)) ^ 2) (measure T) :=
  (pairing_memLp T (DyninMityaginSpace.basis n) 2).integrable_sq

/-- Each basis pairing squared is AEStronglyMeasurable. -/
theorem basis_sq_aestronglyMeasurable (T : E →L[ℝ] H) (n : ℕ) :
    AEStronglyMeasurable (fun ω : Configuration E =>
      (ω (DyninMityaginSpace.basis n)) ^ 2) (measure T) :=
  (basis_sq_integrable T n).aestronglyMeasurable

/-- The enorm sum condition needed for `integral_tsum`: the tsum of
    lintegrals of enorms is finite when T is Hilbert-Schmidt. -/
private theorem enorm_tsum_ne_top (T : E →L[ℝ] H) (hHS : IsHilbertSchmidt T) :
    (∑' n, ∫⁻ ω, ‖(ω (DyninMityaginSpace.basis n)) ^ 2‖ₑ
      ∂(measure T)) ≠ ⊤ := by
  -- Convert enorm of nonneg real to ofReal
  have h_enorm : ∀ n, (∫⁻ ω : Configuration E,
      ‖(ω (DyninMityaginSpace.basis n)) ^ 2‖ₑ ∂(measure T)) =
      ENNReal.ofReal (‖T (DyninMityaginSpace.basis n)‖ ^ 2) := by
    intro n
    rw [show (fun ω : Configuration E =>
        ‖(ω (DyninMityaginSpace.basis n)) ^ 2‖ₑ) =
        (fun ω : Configuration E =>
        ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2))
      from by ext ω; rw [← ofReal_norm_eq_enorm,
                          Real.norm_of_nonneg (sq_nonneg _)]]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (basis_sq_integrable T n) (ae_of_all _ (fun ω => sq_nonneg _))]
    congr 1
    exact basis_second_moment T n
  simp_rw [h_enorm]
  exact hHS.tsum_ofReal_ne_top

/-- The expected squared norm equals the Hilbert-Schmidt norm:
    E[Σₙ |ω(eₙ)|²] = Σₙ ‖T(eₙ)‖² (= HS norm²).

    Each term: E[|ω(eₙ)|²] = ‖T(eₙ)‖² by `second_moment_eq_covariance`.
    The interchange of ∫ and Σ' is justified by `integral_tsum` using
    the nonneg integrability of each squared term.

    This is the key identity connecting the a.s. regularity of samples
    to the Hilbert-Schmidt property of T. -/
theorem expected_norm_sq_eq_hs (T : E →L[ℝ] H) (hHS : IsHilbertSchmidt T) :
    ∫ ω : Configuration E, basisNormSq ω ∂(measure T) =
      hilbertSchmidtNormSq T := by
  simp only [basisNormSq, hilbertSchmidtNormSq]
  rw [integral_tsum (basis_sq_aestronglyMeasurable T) (enorm_tsum_ne_top T hHS)]
  congr 1
  ext n
  exact basis_second_moment T n

/-! ## Forward support theorem -/

/-- If T is Hilbert-Schmidt, the Gaussian measure is supported on
    configurations with finite squared norm Σₙ |ω(eₙ)|² < ∞.

    Proof: We work in ENNReal. The lintegral of the ENNReal-valued
    tsum equals the tsum of lintegrals (by `lintegral_tsum`), each of
    which equals ENNReal.ofReal(‖T eₙ‖²). The tsum is finite by the
    HS condition. By `ae_lt_top`, the ENNReal tsum is a.e. finite,
    which gives real summability. -/
theorem support_of_hilbertSchmidt (T : E →L[ℝ] H) (hHS : IsHilbertSchmidt T) :
    ∀ᵐ ω ∂(measure T), Summable (fun n => (ω (DyninMityaginSpace.basis n)) ^ 2) := by
  -- Define the ENNReal-valued function
  set g : Configuration E → ENNReal :=
    fun ω => ∑' n, ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2) with hg_def
  -- g is measurable (tsum of measurable functions)
  have hg_meas : Measurable g := by
    apply Measurable.ennreal_tsum
    intro n
    exact ENNReal.measurable_ofReal.comp
      ((configuration_eval_measurable (DyninMityaginSpace.basis n)).pow_const 2)
  -- Each component is measurable
  have hg_comp_meas : ∀ n, Measurable (fun ω : Configuration E =>
      ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2)) :=
    fun n => ENNReal.measurable_ofReal.comp
      ((configuration_eval_measurable (DyninMityaginSpace.basis n)).pow_const 2)
  -- ∫⁻ g < ⊤
  have hg_int : ∫⁻ ω, g ω ∂(measure T) ≠ ⊤ := by
    have h_eq_tsum : ∫⁻ ω, g ω ∂(measure T) = ∑' n,
        ∫⁻ ω : Configuration E,
        ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2) ∂(measure T) :=
      lintegral_tsum (fun n => (hg_comp_meas n).aemeasurable)
    rw [h_eq_tsum]
    have h_eq : ∀ n, (∫⁻ ω : Configuration E,
        ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2) ∂(measure T)) =
        ENNReal.ofReal (‖T (DyninMityaginSpace.basis n)‖ ^ 2) := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        (basis_sq_integrable T n) (ae_of_all _ (fun ω => sq_nonneg _))]
      congr 1
      exact basis_second_moment T n
    simp_rw [h_eq]
    exact hHS.tsum_ofReal_ne_top
  -- By ae_lt_top, g(ω) < ⊤ a.e.
  have hg_ae : ∀ᵐ ω ∂(measure T), g ω < ⊤ := ae_lt_top hg_meas hg_int
  -- g(ω) < ⊤ means the ENNReal tsum is finite, hence real summable
  filter_upwards [hg_ae] with ω hω
  have hω' : ∑' n, ENNReal.ofReal ((ω (DyninMityaginSpace.basis n)) ^ 2) < ⊤ := hω
  have h_summ := ENNReal.summable_toReal hω'.ne
  simp only [ENNReal.toReal_ofReal (sq_nonneg _)] at h_summ
  exact h_summ

/-! ## Converse: not HS implies divergence a.s.

The converse requires showing that for independent Gaussian random variables
ω(eₙ) ~ N(0, ‖T(eₙ)‖²) with Σₙ ‖T(eₙ)‖² = ∞, the sum Σₙ |ω(eₙ)|² diverges
a.s. This follows from Kolmogorov's three-series theorem or the 0-1 law for
independent random variables, which are not yet available in Mathlib.

We axiomatize this direction. -/

/-- If T is not Hilbert-Schmidt, the squared basis norm diverges a.s.

    Mathematically: if Σₙ ‖T(eₙ)‖² = ∞, then Σₙ |ω(eₙ)|² = ∞ a.s.,
    because E[|ω(eₙ)|²] = ‖T(eₙ)‖² and the ω(eₙ) are independent
    (by the characteristic functional factoring over orthogonal test
    functions). By Kolmogorov's three-series theorem (or the 0-1 law),
    the sum of independent nonneg random variables with divergent means
    diverges a.s.

    Reference: Shiryaev, "Probability" (1996), Theorem III.3.1. -/
axiom not_supported_of_not_hilbertSchmidt
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [DyninMityaginSpace E]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SeparableSpace H]
    (T : E →L[ℝ] H)
    (hNotHS : ¬ IsHilbertSchmidt T) :
    ∀ᵐ ω ∂(measure T),
      ¬ Summable (fun n => (ω (DyninMityaginSpace.basis n)) ^ 2)

/-! ## Bundled support theorem -/

/-- The Gaussian measure μ_T is supported on the set of configurations
    with finite Cameron-Martin norm iff T is Hilbert-Schmidt.

    Forward direction: HS ⟹ E[Σₙ|ω(eₙ)|²] < ∞ ⟹ a.s. finite.
    Converse: ¬HS ⟹ a.s. divergent by Kolmogorov's three-series theorem. -/
theorem gaussian_support_iff (T : E →L[ℝ] H) :
    IsHilbertSchmidt T ↔
    ∀ᵐ ω ∂(measure T),
      Summable (fun n => (ω (DyninMityaginSpace.basis n)) ^ 2) := by
  constructor
  · exact support_of_hilbertSchmidt T
  · intro h
    by_contra hNotHS
    have h_not := not_supported_of_not_hilbertSchmidt T hNotHS
    -- h : a.e. summable, h_not : a.e. not summable — contradiction
    have h_false : ∀ᵐ ω ∂(measure T), False := by
      filter_upwards [h, h_not] with ω h1 h2
      exact h2 h1
    rw [Filter.eventually_false_iff_eq_bot] at h_false
    haveI := measure_isProbability T
    exact (ae_neBot.mpr (IsProbabilityMeasure.ne_zero (measure T))).ne h_false

end GaussianField
