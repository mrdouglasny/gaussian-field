/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Separation of variables for product eigenfunctions

Pure algebraic lemma: if each `f i : X i → R` satisfies a 1D
"Schrödinger-like" eigenvalue equation
  `-D i (f i) y + V i y · f i y = lam i · f i y`
for some 1D operator `D i : (X i → R) → (X i → R)`, potential `V i : X i → R`,
and eigenvalue `lam i : R`, then the **product function**
`F(x) := ∏ j, f j (x j) : (∀ i, X i) → R` satisfies the multivariate
eigenvalue equation
  `(-∑ i, D i (f i) (x i) · ∏_{j≠i} f j (x j)) + (∑ i, V i (x i)) · F(x)
   = (∑ i, lam i) · F(x)`.

The left-hand side is the coordinate-wise expansion of the multi-D
operator `∑ i (-D i + V i · ·)` acting on `F` (each `(-D i + V i · ·)`
acts on the `i`-th factor, identity on the others).

This is the abstract content of "separation of variables" for product
eigenfunctions. Direct corollaries:

* **Multi-D harmonic oscillator** (`hermiteFunctionNd_HO_eigenvalue`):
  `X i := ℝ`, `D i := iteratedDeriv 2`, `V i := (· ^ 2)`,
  `lam i := 2 (α i) + 1`.
* **Anisotropic HO**: `V i y := ω_i^2 * y^2`, `lam i := ω_i (2 α_i + 1)`.
* **Lattice (discrete) Laplacian**: `X i := ZMod N`, `D i :=` discrete
  finite-difference operator, `V i := 0` (free Laplacian).
* **Higher-derivative separable operators**: `D i := iteratedDeriv n`.
* **Mixed continuum/discrete geometries** (e.g. cylinder `S¹ × ℝ`):
  different `X i` per coordinate.

The proof is **pure `Finset.sum`/`Finset.prod` rearrangement** with
no calculus, which is exactly why "separation of variables" is so
clean: once the 1D eigenvalue equations are in hand, the multi-D
identity is a one-line algebraic manipulation per coordinate.

This lemma is fully generic over the index type, the spatial domain
of each coordinate, and the target commutative ring (e.g. ℝ for real
wavefunctions, ℂ for complex). It is a candidate for upstreaming to
Mathlib (general results on Hilbert space tensor product eigenvalues
currently live in `LinearAlgebra/TensorProduct/...`, but a
pointwise/algebraic version on product eigenfunctions over an
arbitrary commutative ring is missing).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace GaussianField

/-- **Separation of variables for product eigenfunctions** (pointwise
identity, in an arbitrary commutative ring `R`).

If each `f i : X i → R` satisfies the 1D eigenvalue equation
`-D i (f i) y + V i y * f i y = lam i * f i y` for all `y : X i`, then the
product function `F(x) := ∏ j, f j (x j)` satisfies the multivariate
eigenvalue equation
  `(-∑ i, D i (f i) (x i) · ∏_{j≠i} f j (x j)) + (∑ i, V i (x i)) · F(x)
   = (∑ i, lam i) · F(x)`
for every `x : ∀ i, X i`.

The LHS is the standard coordinate-wise expansion of the multi-D
operator `∑ i (-D i + V i · ·)` acting on a product function. The
hypothesis `D i : (X i → R) → (X i → R)` is treated abstractly — `D i`
only appears applied to `f i` at the point `x i`, so it can be any 1D
operator (continuous derivative, discrete finite difference, etc.) for
which the 1D eigenvalue equation holds. -/
theorem separation_of_variables_eigenvalue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} {R : Type*} [CommRing R]
    (f V : ∀ i, X i → R) (lam : ι → R)
    (D : ∀ i, (X i → R) → (X i → R))
    (h_1d : ∀ i y, -D i (f i) y + V i y * f i y = lam i * f i y)
    (x : ∀ i, X i) :
    (-∑ i, D i (f i) (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j)) +
      (∑ i, V i (x i)) * ∏ j, f j (x j) =
    (∑ i, lam i) * ∏ j, f j (x j) := by
  -- Per-`i` factorisation of the full product:
  --   ∏ j, f j (x j) = f i (x i) · ∏ j ∈ univ.erase i, f j (x j).
  have h_prod : ∀ i : ι,
      f i (x i) * ∏ j ∈ Finset.univ.erase i, f j (x j) = ∏ j, f j (x j) :=
    fun i => Finset.mul_prod_erase Finset.univ (fun j => f j (x j))
      (Finset.mem_univ i)
  -- Rewrite `(∑ i, V i (x i)) · F(x)` and `(∑ i, lam i) · F(x)` as
  -- `∑ i, [...] · (f i (x i) · ∏_{j≠i} ...)`.
  have hV : (∑ i, V i (x i)) * ∏ j, f j (x j) =
      ∑ i, V i (x i) * (f i (x i) *
        ∏ j ∈ Finset.univ.erase i, f j (x j)) := by
    simp_rw [h_prod, Finset.sum_mul]
  have hLam : (∑ i, lam i) * ∏ j, f j (x j) =
      ∑ i, lam i * (f i (x i) *
        ∏ j ∈ Finset.univ.erase i, f j (x j)) := by
    simp_rw [h_prod, Finset.sum_mul]
  rw [hV, hLam, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  -- Per-`i` comparison.
  apply Finset.sum_congr rfl
  intro i _
  -- Apply the 1D eigenvalue equation cleanly via `calc + ring`.
  have h_eig := h_1d i (x i)
  set p := ∏ j ∈ Finset.univ.erase i, f j (x j)
  calc -(D i (f i) (x i) * p) + V i (x i) * (f i (x i) * p)
      _ = (-D i (f i) (x i) + V i (x i) * f i (x i)) * p := by ring
      _ = (lam i * f i (x i)) * p                        := by rw [h_eig]
      _ = lam i * (f i (x i) * p)                        := by ring

end GaussianField
