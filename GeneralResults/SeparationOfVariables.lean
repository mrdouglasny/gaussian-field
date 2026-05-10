/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Separation of variables for product eigenfunctions

Pure algebraic lemma: if each `f i : ℝ → ℝ` satisfies a 1D
"Schrödinger-like" eigenvalue equation
  `-D i (f i) y + V i y · f i y = lam i · f i y`
for some 1D operator `D i : (ℝ → ℝ) → (ℝ → ℝ)`, potential `V i : ℝ → ℝ`,
and eigenvalue `lam i : ℝ`, then the **product function**
`F(x) := ∏ j, f j (x j) : (Fin d → ℝ) → ℝ` satisfies the multivariate
eigenvalue equation
  `(-∑ i, D i (f i) (x i) · ∏_{j≠i} f j (x j)) + (∑ i, V i (x i)) · F(x)
   = (∑ i, lam i) · F(x)`.

The left-hand side is the coordinate-wise expansion of the multi-D
operator `∑ i (-D i + V i · ·)` acting on `F` (each `(-D i + V i · ·)`
acts on the `i`-th factor, identity on the others).

This is the abstract content of "separation of variables" for product
eigenfunctions. Direct corollaries:

* **Multi-D harmonic oscillator** (`hermiteFunctionNd_HO_eigenvalue`):
  `D i := iteratedDeriv 2`, `V i := (· ^ 2)`, `lam i := 2 (α i) + 1`.
* **Anisotropic HO**: `V i y := ω_i^2 * y^2`, `lam i := ω_i (2 α_i + 1)`.
* **Higher-derivative separable operators**: `D i := iteratedDeriv n`.
* **General separable Schrödinger**: any `V i` with eigenfunction `f i`.

The proof is **pure `Finset.sum`/`Finset.prod` rearrangement** with
no calculus, which is exactly why "separation of variables" is so
clean: once the 1D eigenvalue equations are in hand, the multi-D
identity is a one-line algebraic manipulation per coordinate.

This lemma is a candidate for upstreaming to Mathlib (general results
on Hilbert space tensor product eigenvalues currently live in
`LinearAlgebra/TensorProduct/...`, but a pointwise/algebraic version
on real-valued products is missing).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

namespace GaussianField

/-- **Separation of variables for product eigenfunctions** (pointwise
identity, real-valued).

If each `f i` satisfies the 1D eigenvalue equation
`-D i (f i) y + V i y * f i y = lam i * f i y` for all `y : ℝ`, then the
product function `F(x) := ∏ j, f j (x j)` satisfies the multivariate
eigenvalue equation
  `(-∑ i, D i (f i) (x i) · ∏_{j≠i} f j (x j)) + (∑ i, V i (x i)) · F(x)
   = (∑ i, lam i) · F(x)`
for every `x : Fin d → ℝ`.

The LHS is the standard coordinate-wise expansion of the multi-D
operator `∑ i (-D i + V i · ·)` acting on a product function. The
hypothesis `D i : (ℝ → ℝ) → (ℝ → ℝ)` is treated abstractly — `D i` only
appears applied to `f i` at the point `x i`, so it can be any 1D
operator (linear or otherwise) for which the 1D eigenvalue equation
holds. -/
theorem separation_of_variables_eigenvalue
    {d : ℕ} (f V : Fin d → ℝ → ℝ) (lam : Fin d → ℝ)
    (D : Fin d → (ℝ → ℝ) → (ℝ → ℝ))
    (h_1d : ∀ i y, -D i (f i) y + V i y * f i y = lam i * f i y)
    (x : Fin d → ℝ) :
    (-∑ i, D i (f i) (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)) +
      (∑ i, V i (x i)) * ∏ j, f j (x j) =
    (∑ i, lam i) * ∏ j, f j (x j) := by
  -- Per-`i` factorisation of the full product:
  --   ∏ j, f j (x j) = f i (x i) · ∏ j ∈ univ.erase i, f j (x j).
  have h_prod : ∀ i : Fin d,
      f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j) = ∏ j, f j (x j) :=
    fun i => Finset.mul_prod_erase Finset.univ (fun j => f j (x j))
      (Finset.mem_univ i)
  -- Rewrite both `(∑ i, V i (x i)) * ∏ j, f j (x j)` and
  -- `(∑ i, lam i) * ∏ j, f j (x j)` as `∑ i [ ... ] * (f i (x i) · ∏_{j≠i} ...)`.
  rw [show (∑ i, V i (x i)) * ∏ j, f j (x j) =
      ∑ i, V i (x i) * (f i (x i) *
        ∏ j ∈ Finset.univ.erase i, f j (x j)) by
        simp_rw [h_prod, Finset.sum_mul],
      show (∑ i, lam i) * ∏ j, f j (x j) =
      ∑ i, lam i * (f i (x i) *
        ∏ j ∈ Finset.univ.erase i, f j (x j)) by
        simp_rw [h_prod, Finset.sum_mul]]
  -- Combine the two LHS sums into a single `∑ i [ ... ]`.
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  -- Per-`i` comparison.
  apply Finset.sum_congr rfl
  intro i _
  -- Set `p := ∏_{j≠i} f j (x j)` for readability.
  set p := ∏ j ∈ Finset.univ.erase i, f j (x j)
  -- Goal:  -(D i (f i) (x i) * p) + V i (x i) * (f i (x i) * p)
  --       = lam i * (f i (x i) * p)
  -- Apply the 1D eigenvalue equation.
  have h_eig := h_1d i (x i)
  -- h_eig: -D i (f i) (x i) + V i (x i) * f i (x i) = lam i * f i (x i)
  linear_combination h_eig * p

end GaussianField
