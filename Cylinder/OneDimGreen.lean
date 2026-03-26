/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.

Ported from Phi4/GreenFunction/OneDimGreen.lean to gaussian-field.
-/
import Cylinder.Basic

/-!
# 1D Green's Function and Reflection Positivity

The 1D Green's function for the operator `(-∂² + λ²)` on ℝ is
  `G_λ(x, y) = (1/(2λ)) exp(-λ|x - y|)`.

The key property for reflection positivity is the **factorization** of the kernel
when the two arguments are on opposite sides of the origin:
  `G_λ(-s, τ) = (1/(2λ)) exp(-λs) exp(-λτ)` for `s, τ > 0`.

This factorization means that the bilinear form `⟨θf, G_λ f⟩` (where `θ` is
time reflection `τ ↦ -τ` and `f` is supported in `τ > 0`) can be written as
a perfect square, hence is non-negative.

## Main results

* `greenKernel1D` — the 1D Green's function `(1/(2λ)) exp(-λ|x-y|)`
* `greenKernel1D_factorization` — factorization for opposite-sign arguments
* `greenKernel1D_reflection_positive` — the RP quadratic form is non-negative

## References

* [Glimm-Jaffe] Section 7.10
-/

noncomputable section

open MeasureTheory Real Set

/-! ## The 1D Green's function -/

/-- The 1D Green's function for `(-∂² + λ²)` on ℝ:
    `G_λ(x, y) = (1/(2λ)) exp(-λ|x - y|)`. -/
def greenKernel1D (lam : ℝ) (x y : ℝ) : ℝ :=
  (1 / (2 * lam)) * Real.exp (-lam * |x - y|)

/-- The Green's function is symmetric. -/
theorem greenKernel1D_symm (lam : ℝ) (x y : ℝ) :
    greenKernel1D lam x y = greenKernel1D lam y x := by
  simp [greenKernel1D, abs_sub_comm]

/-- The Green's function is non-negative for positive λ. -/
theorem greenKernel1D_nonneg (lam : ℝ) (hlam : 0 < lam) (x y : ℝ) :
    0 ≤ greenKernel1D lam x y := by
  unfold greenKernel1D
  apply mul_nonneg
  · apply div_nonneg one_pos.le; linarith
  · exact Real.exp_nonneg _

/-- Diagonal value: `G_λ(x, x) = 1/(2λ)`. -/
theorem greenKernel1D_diag (lam : ℝ) (x : ℝ) :
    greenKernel1D lam x x = 1 / (2 * lam) := by
  simp [greenKernel1D, sub_self, abs_zero]

/-! ## Factorization for opposite-sign arguments

This is the key property for reflection positivity: when the two arguments
are on opposite sides of the origin, the absolute value becomes a sum
and the exponential factors. -/

/-- When `s ≥ 0` and `τ ≥ 0`, we have `|-s - τ| = s + τ`. -/
theorem abs_neg_sub_of_nonneg {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    |(-s) - τ| = s + τ := by
  rw [show (-s) - τ = -(s + τ) by ring, abs_neg]
  exact abs_of_nonneg (add_nonneg hs hτ)

/-- Factorization of the Green's function: for `s, τ ≥ 0`,
    `G_λ(-s, τ) = (1/(2λ)) exp(-λs) exp(-λτ)`.
    This is the key identity for reflection positivity. -/
theorem greenKernel1D_factorization (lam : ℝ) {s τ : ℝ}
    (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    greenKernel1D lam (-s) τ =
      (1 / (2 * lam)) * Real.exp (-lam * s) * Real.exp (-lam * τ) := by
  unfold greenKernel1D
  rw [abs_neg_sub_of_nonneg hs hτ]
  rw [show -lam * (s + τ) = -lam * s + -lam * τ by ring]
  rw [Real.exp_add]
  ring

/-- The "Laplace coefficient" of a function: `L_λ(f) = ∫₀^∞ f(τ) exp(-λτ) dτ`. -/
def laplaceCoeff (lam : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ τ in Ici (0 : ℝ), f τ * Real.exp (-lam * τ)

/-! ## Reflection-positive bilinear form

The RP bilinear form `B(f) = ∫∫_{s,τ≥0} f(s) G(-s, τ) f(τ) ds dτ`
for functions `f` supported on `[0, ∞)` equals
`(1/(2λ)) (L_λ(f))²`, which is manifestly non-negative.

The proof proceeds in two steps:
1. Replace the Green's function with the factored form using
   `greenKernel1D_factorization` (valid since both arguments are non-negative).
2. Factor the double integral into a product of single integrals (Fubini). -/

/-- The integrand in the RP bilinear form equals the factored form
    for non-negative arguments. -/
theorem greenKernel1D_rp_integrand_eq (lam : ℝ) (f : ℝ → ℝ)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    f s * greenKernel1D lam (-s) τ * f τ =
      (1 / (2 * lam)) * (f s * Real.exp (-lam * s)) * (f τ * Real.exp (-lam * τ)) := by
  rw [greenKernel1D_factorization lam hs hτ]
  ring

/-- The RP bilinear form equals a perfect square times `1/(2λ)`.
    This is the core identity for 1D reflection positivity.

    `∫∫_{s,τ≥0} f(s) G(-s, τ) f(τ) ds dτ = (1/(2λ)) (L_λ(f))²`

    The proof uses the factorization of the kernel and Fubini's theorem. -/
theorem greenKernel1D_rp_bilinear_eq_square (lam : ℝ) (hlam : 0 < lam)
    (f : ℝ → ℝ)
    (hf_int : Integrable (fun τ => f τ * Real.exp (-lam * τ))
      (volume.restrict (Ici 0))) :
    ∫ s in Ici (0 : ℝ), ∫ τ in Ici (0 : ℝ),
      f s * greenKernel1D lam (-s) τ * f τ =
    (1 / (2 * lam)) * (laplaceCoeff lam f) ^ 2 := by
  -- Step 1: Replace the integrand using the factorization
  have hcongr_inner : ∀ s, s ∈ Ici (0 : ℝ) →
      (∫ τ in Ici (0 : ℝ), f s * greenKernel1D lam (-s) τ * f τ) =
      (1 / (2 * lam)) * (f s * Real.exp (-lam * s)) * laplaceCoeff lam f := by
    intro s hs
    rw [mem_Ici] at hs
    -- Rewrite inner integral
    have : ∫ τ in Ici (0 : ℝ), f s * greenKernel1D lam (-s) τ * f τ =
        ∫ τ in Ici (0 : ℝ),
          (1 / (2 * lam)) * (f s * Real.exp (-lam * s)) *
          (f τ * Real.exp (-lam * τ)) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro τ hτ
      rw [mem_Ici] at hτ
      exact greenKernel1D_rp_integrand_eq lam f hs hτ
    rw [this]
    -- Pull constant out of integral
    rw [integral_const_mul]
    simp only [laplaceCoeff]
  -- Step 2: Rewrite outer integral
  have houter : ∫ s in Ici (0 : ℝ), ∫ τ in Ici (0 : ℝ),
      f s * greenKernel1D lam (-s) τ * f τ =
    ∫ s in Ici (0 : ℝ),
      (1 / (2 * lam)) * (f s * Real.exp (-lam * s)) * laplaceCoeff lam f := by
    apply setIntegral_congr_fun measurableSet_Ici hcongr_inner
  rw [houter]
  -- Step 3: Pull constants out of outer integral
  rw [show (fun s => (1 / (2 * lam)) * (f s * Real.exp (-lam * s)) * laplaceCoeff lam f) =
    (fun s => (1 / (2 * lam)) * laplaceCoeff lam f * (f s * Real.exp (-lam * s))) from by
    ext s; ring]
  rw [integral_const_mul]
  unfold laplaceCoeff
  ring

/-- The RP bilinear form is non-negative: for any function `f`, the Green's
    function bilinear form with time reflection restricted to `[0,∞)` is
    non-negative.

    `∫∫_{s,τ≥0} f(s) G(-s, τ) f(τ) ds dτ ≥ 0`

    Proof: equals `(1/(2λ)) (L_λ(f))² ≥ 0`. -/
theorem greenKernel1D_reflection_positive (lam : ℝ) (hlam : 0 < lam)
    (f : ℝ → ℝ)
    (hf_int : Integrable (fun τ => f τ * Real.exp (-lam * τ))
      (volume.restrict (Ici 0))) :
    0 ≤ ∫ s in Ici (0 : ℝ), ∫ τ in Ici (0 : ℝ),
      f s * greenKernel1D lam (-s) τ * f τ := by
  rw [greenKernel1D_rp_bilinear_eq_square lam hlam f hf_int]
  apply mul_nonneg
  · apply div_nonneg one_pos.le; linarith
  · exact sq_nonneg _

end
