/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Density in L²(μ) for Sub-Gaussian Probability Measures

A general analysis result: for any probability measure on `Fin n → ℝ` with
sub-Gaussian tails, multivariate polynomials are dense in `L²(μ)`. This is the
natural setting for the moment problem on `ℝⁿ` and the foundation for
orthogonal-polynomial completeness theorems (Hermite, Hermite functions on
`L²(γ)`, Wiener chaos in finite dim).

## Main definitions

- `IsSubGaussianMeasure μ` — `μ` has sub-Gaussian tails:
  `Integrable (fun x => exp(a * ∑ᵢ xᵢ²)) μ` for some `a > 0`. Equivalently,
  `x ↦ exp(a‖x‖²)` is in `L¹(μ)`. All polynomials lie in `L²(μ)` and the
  Gaussian-style tail decay controls polynomial L²-mass on tail balls.

## Main results

- `polynomial_dense_L2_of_subGaussian` (axiom) — multivariate polynomials are
  dense in `L²(μ)` for any sub-Gaussian probability measure `μ` on `Fin n → ℝ`.
- `isSubGaussianMeasure_pi_gaussianReal` — the standard product Gaussian
  `Measure.pi (fun _ : Fin n => gaussianReal 0 1)` has sub-Gaussian tails. Proved
  by transporting **Fernique's theorem** (Mathlib's
  `IsGaussian.exists_integrable_exp_sq`) along
  `WithLp.toLp 2 : (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 2.6.
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer (2006),
  §1.1.1.
- C. Berg, *The multidimensional moment problem and semigroups*, in
  *Probability Measures on Groups VIII*, Lecture Notes in Math. 1210,
  Springer (1986), 110–124.
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

open MeasureTheory ProbabilityTheory Real WithLp

namespace GaussianField.GeneralResults

/-- A measure `μ` on `Fin n → ℝ` has sub-Gaussian tails if there exists `a > 0`
with `Integrable (fun x => exp(a · ∑ᵢ xᵢ²)) μ`.

Equivalently, identifying `Fin n → ℝ` with `EuclideanSpace ℝ (Fin n)`, the function
`x ↦ exp(a‖x‖²)` lies in `L¹(μ)`. This condition makes all polynomial functions
square-integrable under `μ` and is the standard hypothesis for polynomial-density
theorems via the moment-problem circle of ideas. -/
def IsSubGaussianMeasure {n : ℕ} (μ : Measure (Fin n → ℝ)) : Prop :=
  ∃ a > (0 : ℝ), Integrable (fun x : Fin n → ℝ => Real.exp (a * ∑ i, x i ^ 2)) μ

/-- **Polynomial density in L²(μ) for sub-Gaussian probability measures.**

For any probability measure `μ` on `Fin n → ℝ` with sub-Gaussian tails, the
multivariate polynomials `MvPolynomial (Fin n) ℝ` evaluated at coordinates are
dense in `L²(μ)`.

This is the multivariate version of the classical density theorem for the
Hamburger moment problem on determinate measures. The standard product Gaussian,
the Ornstein-Uhlenbeck stationary distribution, and any sub-Gaussian
distribution on `ℝⁿ` (Beta distributions trivially via Stone-Weierstrass on a
compact, Gamma distributions, etc.) all satisfy the hypothesis.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 2.6.

**Proof strategy** (textbook):
1. `Cc(ℝⁿ)` is dense in `L²(μ)` (general measure-theoretic fact, Mathlib has it).
2. Given `g ∈ Cc(ℝⁿ)` supported in a closed ball `B_R`, Stone-Weierstrass on the
   compact `B_R` gives a polynomial `p` with `‖g - p‖_{∞,B_R} < ε`.
3. The sub-Gaussian tail bound `μ(B_R^c) ≤ C exp(-aR²)` controls
   `‖p‖_{L²(B_R^c, μ)}` — polynomial growth on the tail is dominated by Gaussian
   decay of the measure.
4. Combine: `‖f - p‖_{L²(μ)} ≤ ‖f - g‖_{L²(μ)} + ‖g - p‖_{L²(B_R, μ)}
   + ‖p‖_{L²(B_R^c, μ)}`, each term `< ε/3` for suitable choices.

(NOT VERIFIED) -/
axiom polynomial_dense_L2_of_subGaussian {n : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : IsSubGaussianMeasure μ)
    (f : (Fin n → ℝ) → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin n) ℝ,
      (∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂μ) < ε

/-- The standard product Gaussian on `Fin n → ℝ` has sub-Gaussian tails.

The proof transports **Fernique's theorem** for the standard Gaussian on
`EuclideanSpace ℝ (Fin n)` (Mathlib's `IsGaussian.exists_integrable_exp_sq`) back
through the measurable equivalence `WithLp.toLp 2 : (Fin n → ℝ) ≃ EuclideanSpace ℝ (Fin n)`,
under which `Measure.pi (fun _ => gaussianReal 0 1)` pushes forward to
`stdGaussian (EuclideanSpace ℝ (Fin n))` (Mathlib's `map_pi_eq_stdGaussian`).
The Euclidean norm satisfies `‖toLp 2 x‖² = ∑ᵢ xᵢ²`
(`EuclideanSpace.real_norm_sq_eq`). -/
lemma isSubGaussianMeasure_pi_gaussianReal (n : ℕ) :
    IsSubGaussianMeasure
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  -- Fernique: ∃ C > 0, Integrable (fun y => exp(C‖y‖²)) (stdGaussian (EuclideanSpace ℝ (Fin n)))
  obtain ⟨C, hC, hI⟩ :=
    IsGaussian.exists_integrable_exp_sq (μ := stdGaussian (EuclideanSpace ℝ (Fin n)))
  refine ⟨C, hC, ?_⟩
  -- Replace stdGaussian by the pushforward of Measure.pi via toLp 2
  rw [← map_pi_eq_stdGaussian (ι := Fin n)] at hI
  -- Pull the integrability back through toLp 2
  rw [integrable_map_measure ?_ ?_] at hI
  · -- hI : Integrable ((fun y => exp(C * ‖y‖²)) ∘ toLp 2) (Measure.pi ...)
    -- Goal:  Integrable (fun x => exp(C * ∑ i, x i ^ 2))   (Measure.pi ...)
    convert hI using 2 with x
    show Real.exp (C * ∑ i, x i ^ 2) = Real.exp (C * ‖(toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
    rw [EuclideanSpace.real_norm_sq_eq]
  · -- AEStronglyMeasurable of the integrand on EuclideanSpace
    exact (Real.continuous_exp.comp
      ((continuous_const.mul (continuous_norm.pow 2)))).aestronglyMeasurable
  · -- AEMeasurable of toLp 2
    exact (Measurable.aemeasurable (by fun_prop))

end GaussianField.GeneralResults
