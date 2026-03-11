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
- `weighted_support` — weighted-HS ⟹ a.e. weighted-summable

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

/-! ## Weighted Hilbert-Schmidt condition and support -/

/-- Weighted Hilbert-Schmidt condition: Σₙ wₙ ‖T(eₙ)‖² < ∞.
    For Sobolev regularity, take wₙ = (1+λₙ)⁻ˢ where λₙ are eigenvalues
    of the reference operator (e.g., harmonic oscillator). -/
def IsWeightedHS (T : E →L[ℝ] H) (w : ℕ → ℝ) : Prop :=
  Summable (fun n => w n * ‖T (DyninMityaginSpace.basis n)‖ ^ 2)

/-- Weighted basis norm: Σₙ wₙ |ω(eₙ)|². -/
noncomputable def weightedBasisNormSq (w : ℕ → ℝ) (ω : Configuration E) : ℝ :=
  ∑' n, w n * (ω (DyninMityaginSpace.basis n)) ^ 2

/-- Weighted second moment: E[wₙ |ω(eₙ)|²] = wₙ ‖T(eₙ)‖². -/
theorem weighted_basis_second_moment (T : E →L[ℝ] H) (w : ℕ → ℝ)
    (_hw : ∀ n, 0 ≤ w n) (n : ℕ) :
    ∫ ω : Configuration E,
      w n * (ω (DyninMityaginSpace.basis n)) ^ 2 ∂(measure T) =
      w n * ‖T (DyninMityaginSpace.basis n)‖ ^ 2 := by
  rw [MeasureTheory.integral_const_mul, basis_second_moment]

/-- Weighted basis pairing is integrable. -/
theorem weighted_basis_sq_integrable (T : E →L[ℝ] H) (w : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω : Configuration E =>
      w n * (ω (DyninMityaginSpace.basis n)) ^ 2) (measure T) :=
  (basis_sq_integrable T n).const_mul (w n)

/-- If T is weighted-HS with nonneg weights, the Gaussian measure is
    supported on configurations with finite weighted norm Σₙ wₙ|ω(eₙ)|² < ∞.

    Proof: same strategy as `support_of_hilbertSchmidt` — the weight wₙ
    is a constant that passes through the integral, so E[wₙ(ω eₙ)²] = wₙ‖T eₙ‖².
    Summability of these gives finite lintegral, then `ae_lt_top`. -/
theorem weighted_support (T : E →L[ℝ] H) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hWHS : IsWeightedHS T w) :
    ∀ᵐ ω ∂(measure T),
      Summable (fun n => w n * (ω (DyninMityaginSpace.basis n)) ^ 2) := by
  set g : Configuration E → ENNReal :=
    fun ω => ∑' n, ENNReal.ofReal (w n * (ω (DyninMityaginSpace.basis n)) ^ 2)
  have hg_comp_meas : ∀ n, Measurable (fun ω : Configuration E =>
      ENNReal.ofReal (w n * (ω (DyninMityaginSpace.basis n)) ^ 2)) :=
    fun n => ENNReal.measurable_ofReal.comp
      (measurable_const.mul
        ((configuration_eval_measurable (DyninMityaginSpace.basis n)).pow_const 2))
  have hg_meas : Measurable g := Measurable.ennreal_tsum hg_comp_meas
  have hg_int : ∫⁻ ω, g ω ∂(measure T) ≠ ⊤ := by
    have h_eq_tsum : ∫⁻ ω, g ω ∂(measure T) = ∑' n,
        ∫⁻ ω : Configuration E,
        ENNReal.ofReal (w n * (ω (DyninMityaginSpace.basis n)) ^ 2) ∂(measure T) :=
      lintegral_tsum (fun n => (hg_comp_meas n).aemeasurable)
    rw [h_eq_tsum]
    have h_eq : ∀ n, (∫⁻ ω : Configuration E,
        ENNReal.ofReal (w n * (ω (DyninMityaginSpace.basis n)) ^ 2) ∂(measure T)) =
        ENNReal.ofReal (w n * ‖T (DyninMityaginSpace.basis n)‖ ^ 2) := by
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        (weighted_basis_sq_integrable T w n)
        (ae_of_all _ (fun ω => mul_nonneg (hw n) (sq_nonneg _)))]
      congr 1
      exact weighted_basis_second_moment T w hw n
    simp_rw [h_eq]
    exact hWHS.tsum_ofReal_ne_top
  have hg_ae : ∀ᵐ ω ∂(measure T), g ω < ⊤ := ae_lt_top hg_meas hg_int
  filter_upwards [hg_ae] with ω hω
  have h_summ := ENNReal.summable_toReal hω.ne
  simp only [ENNReal.toReal_ofReal (mul_nonneg (hw _) (sq_nonneg _))] at h_summ
  exact h_summ

omit [CompleteSpace H] [SeparableSpace H] in
/-- Unweighted HS is the special case of weighted HS with w = 1. -/
theorem isHilbertSchmidt_eq_weightedHS_one (T : E →L[ℝ] H) :
    IsHilbertSchmidt T ↔ IsWeightedHS T (fun _ => 1) := by
  simp [IsHilbertSchmidt, IsWeightedHS, one_mul]

end GaussianField
