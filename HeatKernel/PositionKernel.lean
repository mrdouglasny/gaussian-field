/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Position-Space Heat Kernel — Axiom Interface

Postulates the position-space heat kernel K((θ,x), (θ',x'), t) on the
cylinder S¹_L × ℝ and its connection to the spectral CLM from `Axioms.lean`.

The kernel factors as:
  K = e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t)

where K_circle is the heat kernel on S¹_L (periodized Gaussian / theta
function) and K_osc is the Mehler kernel (harmonic oscillator heat kernel).

## References

- Reed-Simon, "Methods of Modern Mathematical Physics", Vol. II §X.12 (Mehler)
- Chavel, "Eigenvalues in Riemannian Geometry", Ch. VI (heat kernel on circle)
- docs/position-space-kernel-plan.md
-/

import HeatKernel.Axioms
import SmoothCircle.Basic
import SchwartzNuclear.HermiteFunctions

noncomputable section

open GaussianField GaussianField.SmoothMap_Circle Real MeasureTheory

/-! ## Mehler kernel (harmonic oscillator heat kernel) -/

/-- Mehler kernel: heat kernel for the harmonic oscillator H = -d²/dx² + x².

    Closed form: K(x₁, x₂, t) = (2π sinh 2t)^{-1/2} ·
      exp(-(cosh(2t)(x₁² + x₂²) - 2x₁x₂) / (2 sinh 2t)) -/
noncomputable def mehlerKernel (t x₁ x₂ : ℝ) : ℝ :=
  (2 * π * sinh (2 * t)) ^ (-(1 : ℝ) / 2) *
  exp (-((cosh (2 * t) * (x₁ ^ 2 + x₂ ^ 2) - 2 * x₁ * x₂) /
    (2 * sinh (2 * t))))

/-- The Mehler kernel equals its eigenfunction expansion. -/
axiom mehlerKernel_eq_series (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    mehlerKernel t x₁ x₂ =
      ∑' (k : ℕ), exp (-(t * (2 * ↑k + 1))) *
        hermiteFunction k x₁ * hermiteFunction k x₂

/-- The Mehler series converges absolutely for t > 0. -/
axiom mehlerKernel_summable (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    Summable fun (k : ℕ) => exp (-(t * (2 * ↑k + 1))) *
      hermiteFunction k x₁ * hermiteFunction k x₂

/-- The Mehler kernel is symmetric. -/
theorem mehlerKernel_symmetric (t x₁ x₂ : ℝ) :
    mehlerKernel t x₁ x₂ = mehlerKernel t x₂ x₁ := by
  unfold mehlerKernel; ring_nf

/-- The Mehler kernel is positive for t > 0. -/
axiom mehlerKernel_pos (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    0 < mehlerKernel t x₁ x₂

/-- The Mehler kernel reproduces Hermite eigenfunctions. -/
axiom mehlerKernel_reproduces_hermite (t : ℝ) (ht : 0 < t)
    (k : ℕ) (x₁ : ℝ) :
    ∫ x₂, mehlerKernel t x₁ x₂ * hermiteFunction k x₂ =
      exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₁

/-- The Mehler kernel satisfies the semigroup property. -/
axiom mehlerKernel_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x₁ x₂ : ℝ) :
    ∫ z, mehlerKernel s x₁ z * mehlerKernel t z x₂ =
      mehlerKernel (s + t) x₁ x₂

/-! ## Circle heat kernel -/

/-- Heat kernel on S¹_L, defined as eigenfunction expansion:
    K_circle(θ₁, θ₂, t) = Σ_n e^{-t(2πn/L)²} ψ_n(θ₁) ψ_n(θ₂). -/
noncomputable def circleHeatKernel (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) : ℝ :=
  ∑' (n : ℕ), exp (-(t * (2 * π * ↑n / L) ^ 2)) *
    fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂

/-- The circle heat kernel series converges absolutely for t > 0. -/
axiom circleHeatKernel_summable (L : ℝ) [Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    Summable fun (n : ℕ) => exp (-(t * (2 * π * ↑n / L) ^ 2)) *
      fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂

/-- The circle heat kernel is symmetric. -/
axiom circleHeatKernel_symmetric (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t θ₁ θ₂ = circleHeatKernel L t θ₂ θ₁

/-- The circle heat kernel is positive for t > 0. -/
axiom circleHeatKernel_pos (L : ℝ) [Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    0 < circleHeatKernel L t θ₁ θ₂

/-- The circle heat kernel is L-periodic in the first argument. -/
axiom circleHeatKernel_periodic₁ (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t (θ₁ + L) θ₂ = circleHeatKernel L t θ₁ θ₂

/-- The circle heat kernel is L-periodic in the second argument. -/
axiom circleHeatKernel_periodic₂ (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t θ₁ (θ₂ + L) = circleHeatKernel L t θ₁ θ₂

/-- The circle heat kernel reproduces Fourier eigenfunctions. -/
axiom circleHeatKernel_reproduces_fourier (L : ℝ) [Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (n : ℕ) (θ₁ : ℝ) :
    ∫ θ₂ in (0 : ℝ)..L,
      circleHeatKernel L t θ₁ θ₂ * fourierBasisFun (L := L) n θ₂ =
    exp (-(t * (2 * π * ↑n / L) ^ 2)) * fourierBasisFun (L := L) n θ₁

/-- The circle heat kernel satisfies the semigroup property. -/
axiom circleHeatKernel_semigroup (L : ℝ) [Fact (0 < L)]
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    ∫ θ in (0 : ℝ)..L,
      circleHeatKernel L s θ₁ θ * circleHeatKernel L t θ θ₂ =
    circleHeatKernel L (s + t) θ₁ θ₂

/-! ## Full cylinder heat kernel -/

/-- Heat kernel on S¹_L × ℝ for A = -∂²/∂θ² + (-∂²/∂x² + x²) + m².

    Factors as e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t). -/
noncomputable def cylinderHeatKernel (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) : ℝ :=
  exp (-(mass ^ 2 * t)) * circleHeatKernel L t θ₁ θ₂ * mehlerKernel t x₁ x₂

/-- The cylinder heat kernel equals its eigenfunction expansion. -/
axiom cylinderHeatKernel_eq_series (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (ht : 0 < t) (θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
      ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₁ *
         hermiteFunction (m.unpair).2 x₁) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₂ *
         hermiteFunction (m.unpair).2 x₂)

/-- The cylinder heat kernel is symmetric. -/
theorem cylinderHeatKernel_symmetric (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
    cylinderHeatKernel L mass t θ₂ x₂ θ₁ x₁ := by
  simp only [cylinderHeatKernel,
    circleHeatKernel_symmetric L t θ₁ θ₂,
    mehlerKernel_symmetric t x₁ x₂]

/-- The cylinder heat kernel is positive for t > 0. -/
theorem cylinderHeatKernel_pos (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (ht : 0 < t) (θ₁ x₁ θ₂ x₂ : ℝ) :
    0 < cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  unfold cylinderHeatKernel
  exact mul_pos (mul_pos (exp_pos _) (circleHeatKernel_pos L t ht θ₁ θ₂))
    (mehlerKernel_pos t ht x₁ x₂)

/-- The cylinder heat kernel is L-periodic in θ₁. -/
theorem cylinderHeatKernel_periodic₁ (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t (θ₁ + L) x₁ θ₂ x₂ =
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  simp only [cylinderHeatKernel, circleHeatKernel_periodic₁]

/-- The cylinder heat kernel is L-periodic in θ₂. -/
theorem cylinderHeatKernel_periodic₂ (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ (θ₂ + L) x₂ =
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  simp only [cylinderHeatKernel, circleHeatKernel_periodic₂]

/-! ## Pointwise evaluation and bridge to spectral CLM -/

/-- Evaluate a cylinder test function at a point (θ, x) via the
    eigenfunction expansion:
      f(θ, x) = Σ_m coeff_m(f) · ψ_n(θ) · φ_k(x) -/
noncomputable def cylinderEval (L : ℝ) [Fact (0 < L)]
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) : ℝ :=
  ∑' (m : ℕ), DyninMityaginSpace.coeff m f *
    fourierBasisFun (L := L) (m.unpair).1 θ *
    hermiteFunction (m.unpair).2 x

/-- The eigenfunction expansion converges for cylinder test functions. -/
axiom cylinderEval_summable (L : ℝ) [Fact (0 < L)]
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) :
    Summable fun (m : ℕ) => DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x

/-- **Bridge theorem**: integration against the cylinder heat kernel
    reproduces the spectral CLM action. -/
axiom cylinderHeatKernel_reproduces (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (hmass : 0 < mass) (ht : 0 < t)
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) :
    ∫ θ' in (0 : ℝ)..L, ∫ x',
      cylinderHeatKernel L mass t θ x θ' x' *
        cylinderEval L f θ' x' =
    ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
      DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x

/-- The parameter match between the kernel and heatSingularValue:
    e^{-(s/2)λ_m} = heatSingularValue L mass s m. -/
theorem cylinderHeatKernel_matches_heatSingularValue
    (L mass s : ℝ) (m : ℕ) :
    exp (-(s / 2 * qftEigenvalue L mass m)) =
    heatSingularValue L mass s m := by
  simp [heatSingularValue]

end
