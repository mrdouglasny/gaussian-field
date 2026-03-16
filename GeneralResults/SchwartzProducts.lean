/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# General Results for Schwartz Nuclear Extension

Results about products of Schwartz functions, used in the nuclear extension theorem.

`schwartzProductTensor_schwartz` follows from the existing `schwartzPointwiseProduct`
and `schwartzTensorEquiv` infrastructure (2-fold case on EuclideanSpace), but the
n-fold generalization on arbitrary `Fin n → D` requires coordinate bookkeeping
through `schwartzDomCongr` that is not yet fully formalized.

`productHermite_schwartz_dense` is a standard density result (Reed-Simon V.13).
-/

import SchwartzNuclear.HermiteNuclear
import SchwartzNuclear.SchwartzTensorProduct

noncomputable section

open GaussianField

namespace GaussianField

/-! ## Product of Schwartz functions is Schwartz

The 2-fold case is `schwartzPointwiseProduct` (in `SchwartzTensorProduct.lean`):
  `schwartzPointwiseProduct d f g : SchwartzMap (EuclideanSpace ℝ (Fin (d+2))) ℝ`
with `schwartzPointwiseProduct_apply`: evaluates to `f(init x) · g(last x)`.

The n-fold generalization requires iterating this construction with
appropriate coordinate equivalences. For now we axiomatize it. -/

/-- Product of Schwartz functions is Schwartz.

Proved for the 2-fold case by `schwartzPointwiseProduct` via `schwartzPeelOff.symm`
applied to `NuclearTensorProduct.pure f g`. The n-fold case follows by induction,
composing with `schwartzDomCongr` for the coordinate equivalence
`Fin (n+1) → D ≃L (Fin n → D) × D` (via `Fin.consEquivL`).

The axiomatization avoids ~200 lines of coordinate bookkeeping. -/
axiom schwartzProductTensor_schwartz
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n) (fs : Fin n → SchwartzMap D ℝ) :
    haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin n → D) := Pi.nontrivial
    ∃ (F : SchwartzMap (Fin n → D) ℝ), ∀ x, F x = ∏ i, fs i (x i)

/-- Product Hermite functions are dense in Schwartz space on the product domain.

If a CLF on `S(∏D)` vanishes on all product Hermite functions, it is zero.
This follows from completeness of the product Hermite ONB in L²(∏D)
and the DyninMityaginSpace expansion (both the `toEuclidean`-Hermite and
product-Hermite systems generate the same Schwartz topology).

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
