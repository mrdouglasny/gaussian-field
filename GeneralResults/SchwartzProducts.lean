/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results for Schwartz Nuclear Extension

Textbook axioms about Schwartz spaces that are used in the nuclear extension
theorem. These are standard results from distribution theory that have not
yet been formalized in Lean/Mathlib.

## Axioms

- `schwartzProductTensor_schwartz` — product of Schwartz functions is Schwartz
- `productHermite_schwartz_dense` — product Hermite system is dense in S(∏D)

Both are well-known textbook results (Reed-Simon I, Gel'fand-Vilenkin IV).
They can be proved by:
1. For `schwartzProductTensor_schwartz`: Leibniz rule for iterated derivatives
   of products + rapid decay of each factor in its own variable.
2. For `productHermite_schwartz_dense`: completeness of the product Hermite ONB
   in L²(∏D) + the DyninMityaginSpace expansion implies Schwartz-topology
   density (both the toEuclidean-Hermite and product-Hermite systems generate
   the same Schwartz topology via rapidly decaying change-of-basis matrix).
-/

import SchwartzNuclear.HermiteNuclear

noncomputable section

open GaussianField

namespace GaussianField

/-- **Axiom (product of Schwartz functions is Schwartz).**
If `fᵢ ∈ S(D, ℝ)` for each `i : Fin n`, then `x ↦ ∏ᵢ fᵢ(xᵢ)` is in `S(Fin n → D, ℝ)`.

This is a standard closure property: smoothness by the Leibniz rule for products,
and rapid decay because `|∏ fᵢ(xᵢ)| ≤ ∏ |fᵢ(xᵢ)|` where each factor decays rapidly.

Ref: Reed-Simon I §V.3; Hörmander "Analysis of Linear PDEs" Ch. 7. -/
axiom schwartzProductTensor_schwartz
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n) (fs : Fin n → SchwartzMap D ℝ) :
    haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin n → D) := Pi.nontrivial
    ∃ (F : SchwartzMap (Fin n → D) ℝ), ∀ x, F x = ∏ i, fs i (x i)

/-- **Axiom (product Hermite functions are dense in Schwartz space).**
Every DM basis element of `S(Fin n → D, ℝ)` can be expanded as a
Schwartz-convergent series in product Hermite functions.

Equivalently: if a continuous linear functional on `S(Fin n → D, ℝ)` vanishes
on all product Hermite functions `∏ᵢ ψ_{kᵢ}(xᵢ)`, then it is zero.

This follows from completeness of the product Hermite ONB in L²(∏D) and
the fact that Schwartz-topology convergence of Hermite expansions is
guaranteed by the DM structure (both the `toEuclidean`-Hermite and
product-Hermite systems generate the same Schwartz topology, since they
are related by an L²-orthogonal transformation with rapidly decaying matrix).

Ref: Reed-Simon I, Theorem V.13; Gel'fand-Vilenkin IV §3. -/
axiom productHermite_schwartz_dense
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n)
    (φ : haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
         haveI : Nontrivial (Fin n → D) := Pi.nontrivial
         SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ)
    (hφ : ∀ ks : Fin n → ℕ, ∀ (F : SchwartzMap (Fin n → D) ℝ),
      (∀ x, F x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
      φ F = 0) :
    φ = 0

end GaussianField
