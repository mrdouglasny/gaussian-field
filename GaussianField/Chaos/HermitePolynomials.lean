/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Hermite Polynomials

Defines multivariate (probabilist's) Hermite polynomials on
`Fin n → ℝ` and proves their orthogonality under the standard
multivariate Gaussian measure. Multivariate Hermite is the
tensor product of the 1D Hermite polynomials already in Mathlib
(`Mathlib.RingTheory.Polynomial.Hermite.Basic`).

## Main definitions

- `hermiteMulti α` — multivariate Hermite for multi-index
  `α : Fin n → ℕ`.
- `hermiteMultiEval α x` — its evaluation at `x : Fin n → ℝ`.
- `MultiIndex.totalDegree α` — `∑ i, α i`.

## Main theorems

- `hermiteMulti_orthogonality` — under the standard Gaussian on
  `Fin n → ℝ`, distinct multivariate Hermites are orthogonal,
  and `‖H_α‖² = ∏ᵢ αᵢ!`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §3.1
  (Hermite polynomials) and Theorem 3.21 (orthogonality).
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer
  (2006), §1.1.

## Status

API + axiom skeleton (2026-05-08). Definitions are concrete; the
orthogonality theorem is axiomatized with a textbook citation and
proof-strategy docstring (Fubini on the tensor product + 1D
orthogonality from Mathlib's `Polynomial.hermite_orthogonality`
chain). Awaiting downstream consumer (`WienerChaos.lean`).
-/

import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import SchwartzNuclear.HermiteWick
import GaussianField.WickMultivariate
import GeneralResults.PolynomialDensityGaussian

noncomputable section

open MeasureTheory GaussianField

namespace GaussianField.Chaos

/-- Total degree of a multi-index. -/
def MultiIndex.totalDegree {n : ℕ} (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- Evaluation of the 1D probabilist's Hermite polynomial of degree `k`
at a real point. Wrapper around Mathlib's `Polynomial.hermite`. -/
noncomputable def hermiteEval (k : ℕ) (x : ℝ) : ℝ :=
  ((Polynomial.hermite k).map (Int.castRingHom ℝ)).eval x

/-- Multivariate (probabilist's) Hermite polynomial evaluated at
`x : Fin n → ℝ`: `H_α(x) = ∏ᵢ H_{αᵢ}(xᵢ)`. -/
noncomputable def hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∏ i, hermiteEval (α i) (x i)

/-- The standard multivariate Gaussian measure on `Fin n → ℝ`: product
of `n` copies of the standard 1D Gaussian. -/
noncomputable def stdGaussianFin (n : ℕ) :
    MeasureTheory.Measure (Fin n → ℝ) :=
  MeasureTheory.Measure.pi (fun _ : Fin n => ProbabilityTheory.gaussianReal 0 1)

/-- The 1D probabilist's Hermite polynomial evaluated at `x` equals
the unit-variance Wick monomial, via gaussian-field's `wick_eq_hermiteR`. -/
private lemma hermiteEval_eq_wickMonomial_one (k : ℕ) (x : ℝ) :
    hermiteEval k x = wickMonomial k 1 x := by
  unfold hermiteEval
  rw [wick_eq_hermiteR k 1 (by norm_num : (0:ℝ) < 1)]
  show _ = Real.sqrt 1 ^ k * _
  rw [Real.sqrt_one, one_pow, one_mul, div_one]

/-- **Orthogonality of multivariate Hermite polynomials** under the
standard multivariate Gaussian.

  `∫ H_α(x) · H_β(x) dγ(x) = δ_{αβ} · ∏ᵢ αᵢ!`

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 3.21.

**Proof:** Identify the 1D Hermite evaluation with gaussian-field's
unit-variance Wick monomial (`hermiteEval_eq_wickMonomial_one`),
combine the two products into one product of pairs, apply Fubini on
the pi measure (`integral_fintype_prod_eq_prod`), and reduce each
factor to the 1D Wick orthogonality
`wickMonomial_inner_gaussianReal_one`. -/
theorem hermiteMulti_orthogonality {n : ℕ} (α β : Fin n → ℕ) :
    ∫ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval β x ∂(stdGaussianFin n) =
    if α = β then ((∏ i, (α i).factorial : ℕ) : ℝ) else 0 := by
  -- Step 1: combine the two products into one product of pairs and
  -- replace `hermiteEval` by `wickMonomial _ 1`.
  have h_eq : ∀ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval β x =
      ∏ i, wickMonomial (α i) 1 (x i) * wickMonomial (β i) 1 (x i) := by
    intro x
    unfold hermiteMultiEval
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [hermiteEval_eq_wickMonomial_one, hermiteEval_eq_wickMonomial_one]
  simp_rw [h_eq]
  -- Step 2: Fubini on the pi measure splits the integral as a product.
  unfold stdGaussianFin
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => wickMonomial (α i) 1 x * wickMonomial (β i) 1 x)]
  -- Step 3: each factor is the 1D Wick orthogonality.
  simp_rw [wickMonomial_inner_gaussianReal_one]
  -- Step 4: combine the per-coordinate indicators into the multi-index indicator.
  by_cases hαβ : α = β
  · rw [if_pos hαβ]
    rw [show (∏ i : Fin n,
        if α i = β i then (((α i).factorial : ℕ) : ℝ) else 0) =
        ∏ i : Fin n, ((α i).factorial : ℝ) from by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [if_pos (by rw [hαβ] : α i = β i)]]
    push_cast
    rfl
  · rw [if_neg hαβ]
    -- Some i has α i ≠ β i, so that factor is 0.
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra h
      push Not at h
      exact hαβ (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [if_neg hi]

/-- **Multivariate Hermite polynomials are nonzero in L²(γ).**

Immediate corollary of the orthogonality: `‖H_α‖_{L²}² = ∏ᵢ αᵢ! ≥ 1 > 0`. -/
theorem hermiteMulti_l2_pos {n : ℕ} (α : Fin n → ℕ) :
    0 < ∫ x : Fin n → ℝ,
      hermiteMultiEval α x * hermiteMultiEval α x ∂(stdGaussianFin n) := by
  rw [hermiteMulti_orthogonality, if_pos rfl]
  exact_mod_cast Finset.prod_pos (fun i _ => Nat.factorial_pos (α i))

/-! ## Density of multivariate Hermite polynomials in L²(γ)

The proof of `hermiteMulti_dense` proceeds in two stages:

1. (analytic) Multivariate polynomials are dense in `L²(μ)` for any sub-Gaussian
   probability measure `μ`. This is the textbook density theorem from the
   Hamburger moment problem, postulated as
   `GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian` and applied
   to `stdGaussianFin n` via
   `GaussianField.GeneralResults.isSubGaussianMeasure_pi_gaussianReal`.

2. (algebraic) Every polynomial function `(Fin n → ℝ) → ℝ` of the form
   `MvPolynomial.eval _ p` is a finite ℝ-linear combination of multivariate
   Hermite evaluations. The proof is by `MvPolynomial.induction_on`, using the
   one-dimensional three-term recurrence
   `x · He_{k+1}(x) = He_{k+2}(x) + (k+1) · He_k(x)` to handle multiplication by
   a coordinate.
-/

section HermiteAlgebra

open Polynomial in
/-- Probabilist's Hermite polynomial as `Polynomial ℝ`. -/
private noncomputable def hermitePolyR (k : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite k).map (Int.castRingHom ℝ)

private lemma hermiteEval_eq_eval_hermitePolyR (k : ℕ) (x : ℝ) :
    hermiteEval k x = (hermitePolyR k).eval x := rfl

private lemma derivative_hermitePolyR (k : ℕ) :
    Polynomial.derivative (hermitePolyR (k + 1)) =
      ((k + 1 : ℕ) : Polynomial ℝ) * hermitePolyR k := by
  simp only [hermitePolyR]
  rw [Polynomial.derivative_map, hermite_derivative,
      Polynomial.map_mul, Polynomial.map_natCast]

/-- `hermiteEval 0 x = 1`. -/
private lemma hermiteEval_zero (x : ℝ) : hermiteEval 0 x = 1 := by
  unfold hermiteEval
  simp [Polynomial.hermite_zero]

/-- `hermiteEval 1 x = x`. -/
private lemma hermiteEval_one (x : ℝ) : hermiteEval 1 x = x := by
  unfold hermiteEval
  simp

/-- Three-term recurrence at the value level:
`hermiteEval (k+2) x = x · hermiteEval (k+1) x − (k+1) · hermiteEval k x`. -/
private lemma hermiteEval_recurrence (k : ℕ) (x : ℝ) :
    hermiteEval (k + 2) x =
      x * hermiteEval (k + 1) x - ((k + 1 : ℕ) : ℝ) * hermiteEval k x := by
  show (hermitePolyR (k + 2)).eval x =
    x * (hermitePolyR (k + 1)).eval x - ((k + 1 : ℕ) : ℝ) * (hermitePolyR k).eval x
  have h1 : hermitePolyR (k + 2) =
      Polynomial.X * hermitePolyR (k + 1) -
        Polynomial.derivative (hermitePolyR (k + 1)) := by
    simp only [hermitePolyR]
    rw [Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.derivative_map]
  rw [h1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      derivative_hermitePolyR, Polynomial.eval_mul, Polynomial.eval_natCast]

/-- Equivalent form of the recurrence: `x · He_{k+1}(x) = He_{k+2}(x) + (k+1) · He_k(x)`. -/
private lemma x_mul_hermiteEval_succ (k : ℕ) (x : ℝ) :
    x * hermiteEval (k + 1) x =
      hermiteEval (k + 2) x + ((k + 1 : ℕ) : ℝ) * hermiteEval k x := by
  linarith [hermiteEval_recurrence k x]

/-- Multiplication by `x` at value level for ALL `k` (uniform formula).
For `k = 0`: `x · 1 = He_1(x) + 0 · He_{-1}(_)`. The "He_{-1}" term is
formally `hermiteEval 0 x` paired with coefficient `0` (since `(0 : ℕ) - 1 = 0`
in `ℕ` and the natural-cast coefficient is `0`). -/
private lemma x_mul_hermiteEval (k : ℕ) (x : ℝ) :
    x * hermiteEval k x =
      hermiteEval (k + 1) x + ((k : ℕ) : ℝ) * hermiteEval (k - 1) x := by
  match k with
  | 0 =>
    simp [hermiteEval_zero, hermiteEval_one]
  | k + 1 =>
    show x * hermiteEval (k + 1) x =
      hermiteEval (k + 2) x + ((k + 1 : ℕ) : ℝ) * hermiteEval k x
    exact x_mul_hermiteEval_succ k x

/-- Multiplication by `x_j` on a multivariate Hermite evaluation:
`x_j · ∏_i He_{α_i}(x_i) = He at α with j-coord raised + α_j · He at α with j-coord lowered`. -/
private lemma x_mul_hermiteMultiEval {n : ℕ} (j : Fin n) (α : Fin n → ℕ) (x : Fin n → ℝ) :
    x j * hermiteMultiEval α x =
      hermiteMultiEval (Function.update α j (α j + 1)) x +
      ((α j : ℕ) : ℝ) * hermiteMultiEval (Function.update α j (α j - 1)) x := by
  unfold hermiteMultiEval
  -- Split the product at j
  rw [show (∏ i, hermiteEval (α i) (x i))
        = hermiteEval (α j) (x j) * ∏ i ∈ Finset.univ.erase j, hermiteEval (α i) (x i) from
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm]
  -- Multiply both sides by x_j
  rw [show x j * (hermiteEval (α j) (x j) * ∏ i ∈ Finset.univ.erase j, hermiteEval (α i) (x i))
        = (x j * hermiteEval (α j) (x j)) * ∏ i ∈ Finset.univ.erase j, hermiteEval (α i) (x i) from by
      ring]
  rw [x_mul_hermiteEval]
  -- Now the LHS is (He_{α j + 1}(x j) + α j · He_{α j - 1}(x j)) · prod
  -- The two RHS terms are products in updated α
  have h_upd_succ : ∀ i ∈ Finset.univ.erase j,
      hermiteEval (Function.update α j (α j + 1) i) (x i) = hermiteEval (α i) (x i) := by
    intro i hi
    rw [Function.update_of_ne (by simp at hi; exact hi)]
  have h_upd_pred : ∀ i ∈ Finset.univ.erase j,
      hermiteEval (Function.update α j (α j - 1) i) (x i) = hermiteEval (α i) (x i) := by
    intro i hi
    rw [Function.update_of_ne (by simp at hi; exact hi)]
  rw [show (∏ i, hermiteEval (Function.update α j (α j + 1) i) (x i))
        = hermiteEval (Function.update α j (α j + 1) j) (x j)
          * ∏ i ∈ Finset.univ.erase j, hermiteEval (Function.update α j (α j + 1) i) (x i) from
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm]
  rw [show (∏ i, hermiteEval (Function.update α j (α j - 1) i) (x i))
        = hermiteEval (Function.update α j (α j - 1) j) (x j)
          * ∏ i ∈ Finset.univ.erase j, hermiteEval (Function.update α j (α j - 1) i) (x i) from
      (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm]
  rw [Function.update_self, Function.update_self]
  rw [Finset.prod_congr rfl h_upd_succ, Finset.prod_congr rfl h_upd_pred]
  ring

/-- The ℝ-linear span of multivariate Hermite evaluations as a submodule of
`(Fin n → ℝ) → ℝ`. -/
private noncomputable def hermiteSpan (n : ℕ) :
    Submodule ℝ ((Fin n → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (fun α : Fin n → ℕ => hermiteMultiEval α))

/-- Each `hermiteMultiEval α` is in its own span. -/
private lemma hermiteMultiEval_mem_hermiteSpan {n : ℕ} (α : Fin n → ℕ) :
    (hermiteMultiEval α : (Fin n → ℝ) → ℝ) ∈ hermiteSpan n :=
  Submodule.subset_span ⟨α, rfl⟩

/-- The constant function `1` is in the Hermite span: it equals `hermiteMultiEval 0`. -/
private lemma const_one_mem_hermiteSpan (n : ℕ) :
    ((fun _ : Fin n → ℝ => (1 : ℝ))) ∈ hermiteSpan n := by
  have h : (fun _ : Fin n → ℝ => (1 : ℝ)) = hermiteMultiEval (0 : Fin n → ℕ) := by
    funext x
    unfold hermiteMultiEval
    simp [hermiteEval_zero]
  rw [h]
  exact hermiteMultiEval_mem_hermiteSpan _

/-- The constant function `a` is in the Hermite span. -/
private lemma const_mem_hermiteSpan {n : ℕ} (a : ℝ) :
    ((fun _ : Fin n → ℝ => a)) ∈ hermiteSpan n := by
  have h : (fun _ : Fin n → ℝ => a) = a • (fun _ : Fin n → ℝ => (1 : ℝ)) := by
    funext _; simp
  rw [h]
  exact Submodule.smul_mem _ _ (const_one_mem_hermiteSpan n)

/-- For each generator `hermiteMultiEval α`, multiplication by coordinate `x_j` stays
in the Hermite span (via the three-term recurrence). -/
private lemma x_mul_hermiteMultiEval_mem_hermiteSpan {n : ℕ} (j : Fin n) (α : Fin n → ℕ) :
    ((fun x : Fin n → ℝ => x j * hermiteMultiEval α x)) ∈ hermiteSpan n := by
  have h : (fun x : Fin n → ℝ => x j * hermiteMultiEval α x) =
      hermiteMultiEval (Function.update α j (α j + 1)) +
      ((α j : ℕ) : ℝ) • hermiteMultiEval (Function.update α j (α j - 1)) := by
    funext x
    rw [x_mul_hermiteMultiEval]
    rfl
  rw [h]
  exact Submodule.add_mem _
    (hermiteMultiEval_mem_hermiteSpan _)
    (Submodule.smul_mem _ _ (hermiteMultiEval_mem_hermiteSpan _))

/-- The "multiplication by coordinate `x_j`" linear map preserves the Hermite span. -/
private lemma coord_mul_mem_hermiteSpan {n : ℕ} (j : Fin n) {f : (Fin n → ℝ) → ℝ}
    (hf : f ∈ hermiteSpan n) :
    ((fun x : Fin n → ℝ => x j * f x)) ∈ hermiteSpan n := by
  -- The map `M : g ↦ (x ↦ x_j * g x)` is ℝ-linear.
  let M : ((Fin n → ℝ) → ℝ) →ₗ[ℝ] ((Fin n → ℝ) → ℝ) :=
    { toFun := fun g x => x j * g x
      map_add' := fun g h => by funext x; simp [mul_add]
      map_smul' := fun c g => by funext x; simp [RingHom.id_apply]; ring }
  -- It suffices to show that `Submodule.map M (hermiteSpan n) ≤ hermiteSpan n`.
  have h_le : Submodule.map M (hermiteSpan n) ≤ hermiteSpan n := by
    rw [hermiteSpan, Submodule.map_span_le]
    rintro g ⟨α, rfl⟩
    exact x_mul_hermiteMultiEval_mem_hermiteSpan j α
  exact h_le ⟨f, hf, rfl⟩

/-- Every multivariate polynomial evaluates to a function in the Hermite span. -/
private lemma mvPolynomial_eval_mem_hermiteSpan {n : ℕ}
    (p : MvPolynomial (Fin n) ℝ) :
    ((fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) p)) ∈ hermiteSpan n := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) (MvPolynomial.C a))
        = (fun _ : Fin n → ℝ => a) := by
      funext x; simp
    rw [h]
    exact const_mem_hermiteSpan a
  | add p q hp hq =>
    have h : (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) (p + q))
        = (fun x => MvPolynomial.eval (fun i => x i) p) +
          (fun x => MvPolynomial.eval (fun i => x i) q) := by
      funext x; simp
    rw [h]
    exact Submodule.add_mem _ hp hq
  | mul_X q j hq =>
    have h : (fun x : Fin n → ℝ => MvPolynomial.eval (fun i => x i) (q * MvPolynomial.X j))
        = (fun x => x j * MvPolynomial.eval (fun i => x i) q) := by
      funext x; simp; ring
    rw [h]
    exact coord_mul_mem_hermiteSpan j hq

/-- Extract a finite Hermite combination from membership in the span. -/
private lemma exists_hermite_combination_of_mem_hermiteSpan {n : ℕ}
    {f : (Fin n → ℝ) → ℝ} (hf : f ∈ hermiteSpan n) :
    ∃ (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ),
      ∀ x, f x = ∑ α ∈ s, c α * hermiteMultiEval α x := by
  classical
  refine Submodule.span_induction (p := fun f _ =>
    ∃ (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ),
      ∀ x, f x = ∑ α ∈ s, c α * hermiteMultiEval α x) ?_ ?_ ?_ ?_ hf
  · -- mem case
    rintro g ⟨α, rfl⟩
    refine ⟨{α}, fun β => if β = α then 1 else 0, fun x => ?_⟩
    rw [Finset.sum_singleton]
    show hermiteMultiEval α x = (if α = α then 1 else 0) * hermiteMultiEval α x
    rw [if_pos rfl, one_mul]
  · -- zero case
    exact ⟨∅, fun _ => 0, fun x => by simp⟩
  · -- add case
    rintro g h _ _ ⟨s_g, c_g, h_g⟩ ⟨s_h, c_h, h_h⟩
    refine ⟨s_g ∪ s_h, fun α =>
      (if α ∈ s_g then c_g α else 0) + (if α ∈ s_h then c_h α else 0),
      fun x => ?_⟩
    show g x + h x = _
    rw [h_g, h_h]
    -- Rewrite each sum over the union with an indicator function.
    have h_sum_g :
        (∑ α ∈ s_g, c_g α * hermiteMultiEval α x) =
        ∑ α ∈ s_g ∪ s_h,
          (if α ∈ s_g then c_g α else 0) * hermiteMultiEval α x := by
      rw [show (∑ α ∈ s_g, c_g α * hermiteMultiEval α x) =
            ∑ α ∈ s_g, (if α ∈ s_g then c_g α else 0) * hermiteMultiEval α x from by
        refine Finset.sum_congr rfl ?_
        intro α hα; rw [if_pos hα]]
      exact Finset.sum_subset Finset.subset_union_left
        (fun α _ hα_not => by rw [if_neg hα_not, zero_mul])
    have h_sum_h :
        (∑ α ∈ s_h, c_h α * hermiteMultiEval α x) =
        ∑ α ∈ s_g ∪ s_h,
          (if α ∈ s_h then c_h α else 0) * hermiteMultiEval α x := by
      rw [show (∑ α ∈ s_h, c_h α * hermiteMultiEval α x) =
            ∑ α ∈ s_h, (if α ∈ s_h then c_h α else 0) * hermiteMultiEval α x from by
        refine Finset.sum_congr rfl ?_
        intro α hα; rw [if_pos hα]]
      exact Finset.sum_subset Finset.subset_union_right
        (fun α _ hα_not => by rw [if_neg hα_not, zero_mul])
    rw [h_sum_g, h_sum_h, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro α _
    ring
  · -- smul case
    rintro a g _ ⟨s, c, h_g⟩
    refine ⟨s, fun α => a * c α, fun x => ?_⟩
    show a • g x = _
    rw [h_g, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro α _
    show a * (c α * _) = a * c α * _
    ring

end HermiteAlgebra

/-- **Density of multivariate Hermite polynomials in L²(γ).**

The polynomial subalgebra generated by the coordinate functions $\{x_i\}$ is dense
in $L^2(\gamma_n)$ for $\gamma_n$ the standard product Gaussian. By Gram-Schmidt
on the multivariate Hermite family (which is graded-orthogonal by total degree
under the standard Gaussian), the Hermite family forms a complete orthogonal
system.

**Proof:** Combine
- `GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian` (axiom):
  multivariate polynomials are dense in `L²(μ)` for any sub-Gaussian probability
  measure on `Fin n → ℝ`.
- `GaussianField.GeneralResults.isSubGaussianMeasure_pi_gaussianReal` (proved):
  the standard product Gaussian satisfies the sub-Gaussian condition (transported
  from Mathlib's `IsGaussian.exists_integrable_exp_sq`).
- `mvPolynomial_eval_isHermiteCombo` (proved): every polynomial-evaluation
  function is a finite ℝ-linear combination of multivariate Hermite evaluations
  (via `MvPolynomial.induction_on` + 1D three-term recurrence).

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 2.6 + Theorem 3.21. -/
theorem hermiteMulti_dense {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hf : MeasureTheory.MemLp f 2 (stdGaussianFin n))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ),
      (∫ x, |f x - ∑ α ∈ s, c α * hermiteMultiEval α x| ^ 2 ∂(stdGaussianFin n)) < ε := by
  haveI : MeasureTheory.IsProbabilityMeasure (stdGaussianFin n) := by
    unfold stdGaussianFin
    infer_instance
  have hSG :
      GaussianField.GeneralResults.IsSubGaussianMeasure (stdGaussianFin n) :=
    GaussianField.GeneralResults.isSubGaussianMeasure_pi_gaussianReal n
  obtain ⟨p, hp⟩ :=
    GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian
      (stdGaussianFin n) hSG f hf ε hε
  have h_mem := mvPolynomial_eval_mem_hermiteSpan p
  obtain ⟨s, c, hsc⟩ := exists_hermite_combination_of_mem_hermiteSpan h_mem
  refine ⟨s, c, ?_⟩
  have h_eq : ∀ x, |f x - ∑ α ∈ s, c α * hermiteMultiEval α x| ^ 2 =
      |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 := by
    intro x; rw [hsc x]
  rw [show (∫ x, |f x - ∑ α ∈ s, c α * hermiteMultiEval α x| ^ 2 ∂(stdGaussianFin n)) =
      ∫ x, |f x - MvPolynomial.eval (fun i => x i) p| ^ 2 ∂(stdGaussianFin n) from
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_eq)]
  exact hp

end GaussianField.Chaos
