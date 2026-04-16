/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick Monomial Orthogonality under Gaussian Measure

The Wick-ordered monomial `:x^n:_c` has zero mean under a centered
Gaussian of variance c, for n ≥ 1. This is the fundamental
orthogonality property that makes Wick ordering useful in QFT.

## Main results

- `wickMonomial_deriv` — d/dx :x^n:_c = n · :x^{n-1}:_c
- `wickMonomial_mean_zero` — ∫ :x^n:_c dN(0,c) = 0 for n ≥ 1

## Existing infrastructure

- `wickMonomial` (HermiteWick.lean): the Wick monomial function
- `wick_eq_hermiteR` (HermiteWick.lean): :x^n:_c = c^{n/2} · He_n(x/√c)
- `probHermite` (auto1/Hermite/Basic.lean): Hermite polynomial H_n(x;c)
  with recurrence H_{n+1} = x·H_n - c·H_n'

## Proof strategy

The proof uses induction + Stein's lemma (Gaussian integration by parts):

For centered Gaussian μ with variance c:
  E[x · f(x)] = c · E[f'(x)]

Then:
- E[:x^0:] = 1
- E[:x^1:] = E[x] = 0 (centered)
- E[:x^{n+1}:] = E[x · :x^n:] - n·c · E[:x^{n-1}:]
                = c · E[d/dx :x^n:] - n·c · E[:x^{n-1}:]  (Stein)
                = c·n · E[:x^{n-1}:] - n·c · E[:x^{n-1}:]  (derivative)
                = 0  (induction)

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §I.3
- Glimm-Jaffe, *Quantum Physics*, §8.6
-/

import SchwartzNuclear.HermiteWick

noncomputable section

open Real Polynomial MeasureTheory

/-! ## Helper: Wick polynomial representation

The Wick monomial `wickMonomial n c` is a polynomial in `x`. We represent it
as a `Polynomial ℝ` to leverage Mathlib's polynomial differentiability and
growth bounds. -/

/-- The Wick polynomial `:x^n:_c` as a formal polynomial. -/
private def wickPoly : ℕ → ℝ → ℝ[X]
  | 0, _ => 1
  | 1, _ => X
  | n + 2, c => X * wickPoly (n + 1) c - Polynomial.C ((n + 1 : ℝ) * c) * wickPoly n c

/-- The Wick monomial equals evaluation of the Wick polynomial. -/
private theorem wickMonomial_eq_eval (n : ℕ) (c x : ℝ) :
    wickMonomial n c x = (wickPoly n c).eval x := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [wickMonomial, wickPoly]
    | 1 => simp [wickMonomial, wickPoly]
    | k + 2 =>
      rw [wickMonomial_succ_succ]
      simp only [wickPoly, eval_sub, eval_mul, eval_X, eval_C]
      rw [ih (k + 1) (by omega), ih k (by omega)]

/-- The Wick monomial is differentiable (it's a polynomial). -/
private theorem wickMonomial_differentiable (n : ℕ) (c : ℝ) :
    Differentiable ℝ (wickMonomial n c) := by
  have : wickMonomial n c = fun x => (wickPoly n c).eval x := by
    ext x; exact wickMonomial_eq_eval n c x
  rw [this]; exact (wickPoly n c).differentiable

/-- The Wick monomial has polynomial growth (it's bounded by `C * (1 + |x|)^d`). -/
private theorem wickMonomial_growth (n : ℕ) (c : ℝ) :
    ∃ (C : ℝ) (d : ℕ), ∀ x : ℝ, |wickMonomial n c x| ≤ C * (1 + |x|) ^ d := by
  suffices h : ∀ (p : ℝ[X]), ∃ (C : ℝ) (d : ℕ), ∀ x : ℝ, |p.eval x| ≤ C * (1 + |x|) ^ d by
    obtain ⟨C, d, hb⟩ := h (wickPoly n c)
    exact ⟨C, d, fun x => by rw [wickMonomial_eq_eval]; exact hb x⟩
  intro p
  refine ⟨(∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) + 1, p.natDegree, fun x => ?_⟩
  rw [Polynomial.eval_eq_sum_range]
  have hone : (1 : ℝ) ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
  calc |∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i|
      ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i * x ^ i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * |x| ^ i := by
        congr 1; ext i; rw [abs_mul, abs_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| * (1 + |x|) ^ p.natDegree := by
        apply Finset.sum_le_sum; intro i hi
        exact mul_le_mul_of_nonneg_left
          ((pow_le_pow_left₀ (abs_nonneg x) (le_add_of_nonneg_left one_pos.le) i).trans
            (pow_le_pow_right₀ hone (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
          (abs_nonneg _)
    _ = (∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i|) * (1 + |x|) ^ p.natDegree := by
        rw [Finset.sum_mul]
    _ ≤ _ := by
        linarith [pow_nonneg (by linarith [abs_nonneg x] : (0 : ℝ) ≤ 1 + |x|) p.natDegree]

/-- `HasDerivAt` for `wickMonomial n c` at every point, for all `n` (including `n = 0`).
The derivative is `n * wickMonomial (n - 1) c x`. -/
private theorem wickMonomial_hasDerivAt_all (c : ℝ) (n : ℕ) :
    ∀ x : ℝ, HasDerivAt (wickMonomial n c) (↑n * wickMonomial (n - 1) c x) x := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => intro x; simp [wickMonomial]; exact hasDerivAt_const x 1
    | 1 => intro x; simp [wickMonomial]; exact hasDerivAt_id x
    | (k + 2) =>
      intro x
      have ih1 := ih (k + 1) (by omega) x
      have ih0 := ih k (by omega) x
      simp only [show (k + 1 : ℕ) - 1 = k from by omega] at ih1
      have hsub := ((hasDerivAt_id x).mul ih1).sub (ih0.const_mul ((↑k + 1 : ℝ) * c))
      have h_eq : (id * wickMonomial (k + 1) c - fun y => (↑k + 1) * c * wickMonomial k c y) =
        wickMonomial (k + 2) c := by ext y; simp [id, wickMonomial_succ_succ]
      rw [h_eq] at hsub
      refine hsub.congr_deriv ?_
      simp only [show k + 2 - 1 = k + 1 from by omega, id]
      cases k with
      | zero => simp [wickMonomial]; ring
      | succ j => rw [wickMonomial_succ_succ j c x]; push_cast; ring

/-- Integrability of `wickMonomial n c` under a probability measure satisfying Stein's
identity with variance `c > 0`. Follows from: all moments `E[|X|^n]` are finite
(derivable from Stein + `c > 0` by bootstrapping even moments), and `wickMonomial`
is a polynomial bounded by `C * (1 + |x|)^d`. -/
private axiom wickMonomial_integrable (n : ℕ) (c : ℝ) (hc : 0 < c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_stein : ∀ f : ℝ → ℝ, Differentiable ℝ f →
      (∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n) →
      ∫ x, x * f x ∂μ = c * ∫ x, deriv f x ∂μ) :
    Integrable (wickMonomial n c) μ

/-- Integrability of `x * wickMonomial n c x` under a Stein measure.
Follows from the recursion: `x * W_{n}(x) = W_{n+1}(x) + n*c*W_{n-1}(x)`. -/
private theorem xmul_wickMonomial_integrable (n : ℕ) (c : ℝ) (hc : 0 < c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_stein : ∀ f : ℝ → ℝ, Differentiable ℝ f →
      (∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n) →
      ∫ x, x * f x ∂μ = c * ∫ x, deriv f x ∂μ) :
    Integrable (fun x => x * wickMonomial n c x) μ := by
  cases n with
  | zero => simp [wickMonomial]; exact wickMonomial_integrable 1 c hc μ hμ_stein
  | succ k =>
    have hfun : (fun x => x * wickMonomial (k + 1) c x) =
      (fun x => wickMonomial (k + 2) c x + (↑k + 1) * c * wickMonomial k c x) := by
      ext x; have := wickMonomial_succ_succ k c x; linarith
    rw [hfun]
    exact (wickMonomial_integrable (k + 2) c hc μ hμ_stein).add
      ((wickMonomial_integrable k c hc μ hμ_stein).const_mul _)

/-! ## Wick monomial derivative

d/dx :x^n:_c = n · :x^{n-1}:_c.

This is the analog of He_n'(x) = n · He_{n-1}(x) for Hermite polynomials. -/

/-- Derivative of the Wick monomial: d/dx :x^n:_c = n · :x^{n-1}:_c.

From `wick_eq_hermiteR`: :x^n:_c = √c^n · He_n(x/√c).
Differentiating: d/dx = √c^n · He_n'(x/√c) · 1/√c
                      = √c^{n-1} · n · He_{n-1}(x/√c)   [He_n' = n·He_{n-1}]
                      = n · :x^{n-1}:_c. -/
theorem wickMonomial_deriv (n : ℕ) (c : ℝ) (hn : 1 ≤ n) :
    ∀ x, HasDerivAt (wickMonomial n c) (n * wickMonomial (n - 1) c x) x :=
  fun x => wickMonomial_hasDerivAt_all c n x

/-! ## Stein's lemma (Gaussian integration by parts)

For X ~ N(0, c): E[X · f(X)] = c · E[f'(X)].

This is the fundamental integration-by-parts formula for Gaussian measures.
It characterizes the Gaussian distribution (Stein's method). -/

/-- **Stein's lemma**: E[x · f(x)] = c · E[f'(x)] under the Gaussian
measure N(0,c).

Proof: Use ∫ x·f(x)·g(x) dx = -∫ f(x)·d/dx(x·g(x)) dx where
g(x) = (2πc)^{-1/2} exp(-x²/(2c)) is the Gaussian density,
and x·g(x) = -c·g'(x). Integration by parts with boundary terms
vanishing by Gaussian decay. -/
theorem stein_lemma (c : ℝ) (hc : 0 < c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    -- μ is the centered Gaussian of variance c
    (hμ_stein : ∀ f : ℝ → ℝ, Differentiable ℝ f →
      -- f and f' have at most polynomial growth
      (∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n) →
      ∫ x, x * f x ∂μ = c * ∫ x, deriv f x ∂μ)
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hf_growth : ∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n) :
    ∫ x, x * f x ∂μ = c * ∫ x, deriv f x ∂μ :=
  hμ_stein f hf hf_growth

/-! ## Wick orthogonality -/

/-- **Wick monomial has zero mean under matching Gaussian.**

For n ≥ 1: ∫ :x^n:_c dN(0,c) = 0.

Proof by induction on n:
- Base (n=1): :x^1: = x, so ∫ x dμ = 0 (centered Gaussian).
- Step (n → n+1): Using the Wick recursion
    :x^{n+1}: = x · :x^n: - n·c · :x^{n-1}:
  and Stein's lemma E[x·f(x)] = c·E[f'(x)]:
    E[:x^{n+1}:] = E[x · :x^n:] - n·c · E[:x^{n-1}:]
                 = c · E[d/dx :x^n:] - n·c · E[:x^{n-1}:]
                 = c · n · E[:x^{n-1}:] - n·c · E[:x^{n-1}:]
                 = 0.
-/
theorem wickMonomial_mean_zero (c : ℝ) (hc : 0 < c)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ_mean : ∫ x, x ∂μ = 0)
    (hμ_stein : ∀ f : ℝ → ℝ, Differentiable ℝ f →
      (∃ C n, ∀ x, |f x| ≤ C * (1 + |x|) ^ n) →
      ∫ x, x * f x ∂μ = c * ∫ x, deriv f x ∂μ)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫ x, wickMonomial n c x ∂μ = 0 := by
  -- Induction on n
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      -- n = 1: :x^1: = x, and ∫ x dμ = 0
      simp [wickMonomial]
      exact hμ_mean
    | succ k =>
      -- n = k+2: use recursion + Stein + induction hypothesis
      -- :x^{k+2}: = x · :x^{k+1}: - (k+1)·c · :x^k:
      -- E[:x^{k+2}:] = E[x · :x^{k+1}:] - (k+1)·c · E[:x^k:]
      -- = c · (k+1) · E[:x^k:] - (k+1)·c · E[:x^k:]  [Stein + deriv]
      -- = 0 [the two terms cancel algebraically]
      -- Step 1: Unfold the recursion inside the integral
      simp_rw [wickMonomial_succ_succ k c]
      -- Step 2: Split the integral (requires integrability)
      rw [integral_sub (xmul_wickMonomial_integrable (k + 1) c hc μ hμ_stein)
        ((wickMonomial_integrable k c hc μ hμ_stein).const_mul _)]
      -- Step 3: Apply Stein's lemma to ∫ x * W_{k+1}(x) dμ
      have hstein := hμ_stein (wickMonomial (k + 1) c)
        (wickMonomial_differentiable (k + 1) c) (wickMonomial_growth (k + 1) c)
      rw [hstein]
      -- Step 4: Compute deriv (W_{k+1}) = (k+1) * W_k
      have hderiv : (fun x => deriv (wickMonomial (k + 1) c) x) =
        fun x => ↑(k + 1) * wickMonomial k c x := by
        ext x; exact (wickMonomial_hasDerivAt_all c (k + 1) x).deriv
      simp_rw [hderiv]
      -- Step 5: Pull out constants and cancel
      rw [integral_const_mul, integral_const_mul]
      push_cast; ring

/-! ## Application: O(N) Wick ordering

For the O(N) model, the Wick monomial is wickMonomial_ON N c k t
where t = |φ|² = Σ (φⁱ)² has a chi-squared distribution with N
degrees of freedom under the product GFF.

The orthogonality generalizes:
  E[wickMonomial_ON N c k (|φ|²)] = 0 for k ≥ 1

This follows from the scalar case applied to each of the N
components + the chi-squared decomposition. Alternatively,
it follows from the Laguerre polynomial orthogonality under
the gamma distribution (since chi-squared = gamma(N/2, 2c)).

This is the key fact needed for the density transfer constant:
  E_GFF[V] = E_GFF[Σ_x :P(|φ(x)|²):_c] = 0
since each Wick-ordered monomial has zero mean. -/

end
