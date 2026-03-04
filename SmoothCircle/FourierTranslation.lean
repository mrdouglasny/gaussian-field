/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Coefficient Transformation under Circle Symmetries

Axiomatizes how real Fourier coefficients transform under translation
and reflection on the circle, and proves the paired-product invariance
that underpins Green's function symmetry.

## Main axioms

- `fourierCoeffReal_circleTranslation_zero` — constant mode is translation-invariant
- `fourierCoeffReal_circleTranslation_cos` — cos mode rotation under translation
- `fourierCoeffReal_circleTranslation_sin` — sin mode rotation under translation
- `fourierCoeffReal_circleReflection_zero` — constant mode is reflection-invariant
- `fourierCoeffReal_circleReflection_cos` — cos modes are even (reflection-invariant)
- `fourierCoeffReal_circleReflection_sin` — sin modes are odd (negated by reflection)

## Main theorems

- `paired_coeff_product_circleTranslation` — `Σ c_n(Tf)c_n(Tg)` is
  invariant over paired cos/sin modes (from cos²+sin²=1)

## Mathematical background

Translation `(T_v f)(x) = f(x - v)` acts on the real Fourier basis by
rotating cos/sin pairs:
  `c_{2k-1}(T_v f) = cos(θ)·c_{2k-1}(f) - sin(θ)·c_{2k}(f)`
  `c_{2k}(T_v f) = sin(θ)·c_{2k-1}(f) + cos(θ)·c_{2k}(f)`
where `θ = 2πkv/L`.

Reflection `(Θf)(x) = f(-x)` preserves cosines and negates sines:
  `c_{2k-1}(Θf) = c_{2k-1}(f)`, `c_{2k}(Θf) = -c_{2k}(f)`

## References

- Grafakos, *Classical Fourier Analysis*, §3.1
- Katznelson, *An Introduction to Harmonic Analysis*, Ch. I
-/

import SmoothCircle.Eigenvalues
import Torus.Symmetry

noncomputable section

namespace GaussianField

open SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Translation axioms -/

/-- **Constant mode is translation-invariant.**

  `c₀(T_v f) = c₀(f)`

The constant Fourier mode `∫₀ᴸ f(x)/√L dx` is unchanged by
translation because integration over a full period is shift-invariant.

Proof sketch: `c₀(T_v f) = ∫₀ᴸ f(x-v)/√L dx = ∫₀ᴸ f(y)/√L dy = c₀(f)`
by the substitution `y = x - v` and L-periodicity of the integrand. -/
axiom fourierCoeffReal_circleTranslation_zero (v : ℝ)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) 0 (circleTranslation L v f) =
    fourierCoeffReal (L := L) 0 f

/-- **Cosine mode transforms under translation by rotation.**

  `c_{2k-1}(T_v f) = cos(2πkv/L)·c_{2k-1}(f) - sin(2πkv/L)·c_{2k}(f)`

The cosine coefficient at frequency k picks up a rotation by the phase
angle `θ = 2πkv/L`. This is the real-basis version of the standard
result `f̂(n)(T_v f) = e^{2πinv/L} f̂(n)(f)`.

Proof sketch: Expand `c_{2k-1}(T_v f) = ∫ f(x-v)·√(2/L)·cos(2πkx/L) dx`,
substitute `y = x - v`, apply `cos(a+b) = cos(a)cos(b) - sin(a)sin(b)`,
and identify the resulting integrals as `c_{2k-1}(f)` and `c_{2k}(f)`. -/
axiom fourierCoeffReal_circleTranslation_cos (k : ℕ) (hk : 0 < k)
    (v : ℝ) (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleTranslation L v f) =
    Real.cos (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k - 1) f -
    Real.sin (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k) f

/-- **Sine mode transforms under translation by rotation.**

  `c_{2k}(T_v f) = sin(2πkv/L)·c_{2k-1}(f) + cos(2πkv/L)·c_{2k}(f)`

The sine coefficient at frequency k picks up the complementary rotation.
Together with the cosine axiom, this says translation acts by SO(2) rotation
on each (cos, sin) pair at frequency k.

Proof sketch: Expand `c_{2k}(T_v f) = ∫ f(x-v)·√(2/L)·sin(2πkx/L) dx`,
substitute `y = x - v`, apply `sin(a+b) = sin(a)cos(b) + cos(a)sin(b)`,
and identify the resulting integrals as `c_{2k-1}(f)` and `c_{2k}(f)`. -/
axiom fourierCoeffReal_circleTranslation_sin (k : ℕ) (hk : 0 < k)
    (v : ℝ) (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k) (circleTranslation L v f) =
    Real.sin (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k - 1) f +
    Real.cos (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k) f

/-! ## Reflection axioms -/

/-- **Constant mode is reflection-invariant.**

  `c₀(Θf) = c₀(f)`

The constant mode is even under reflection. -/
axiom fourierCoeffReal_circleReflection_zero
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) 0 (circleReflection L f) =
    fourierCoeffReal (L := L) 0 f

/-- **Cosine modes are even under reflection.**

  `c_{2k-1}(Θf) = c_{2k-1}(f)`

Cosine is an even function: `cos(-x) = cos(x)`, so
`∫ f(-x) cos(2πkx/L) dx = ∫ f(y) cos(2πky/L) dy`.

Proof sketch: `c_{2k-1}(Θf) = ∫₀ᴸ f(-x) √(2/L) cos(2πkx/L) dx`.
Substitute `y = -x`: `= ∫₀ᴸ f(y) √(2/L) cos(-2πky/L) dy`
`= ∫₀ᴸ f(y) √(2/L) cos(2πky/L) dy = c_{2k-1}(f)`. -/
axiom fourierCoeffReal_circleReflection_cos (k : ℕ) (hk : 0 < k)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleReflection L f) =
    fourierCoeffReal (L := L) (2 * k - 1) f

/-- **Sine modes are odd under reflection.**

  `c_{2k}(Θf) = -c_{2k}(f)`

Sine is an odd function: `sin(-x) = -sin(x)`, so
`∫ f(-x) sin(2πkx/L) dx = -∫ f(y) sin(2πky/L) dy`.

Proof sketch: `c_{2k}(Θf) = ∫₀ᴸ f(-x) √(2/L) sin(2πkx/L) dx`.
Substitute `y = -x`: `= -∫₀ᴸ f(y) √(2/L) sin(2πky/L) dy = -c_{2k}(f)`. -/
axiom fourierCoeffReal_circleReflection_sin (k : ℕ) (hk : 0 < k)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k) (circleReflection L f) =
    -(fourierCoeffReal (L := L) (2 * k) f)

/-! ## Paired product invariance -/

/-- **Paired product of Fourier coefficients is translation-invariant.**

For each frequency k ≥ 1, the sum of products over the paired
cos/sin modes is invariant under translation:

  `c_{2k-1}(Tf)·c_{2k-1}(Tg) + c_{2k}(Tf)·c_{2k}(Tg)`
  `= c_{2k-1}(f)·c_{2k-1}(g) + c_{2k}(f)·c_{2k}(g)`

This is purely algebraic: if `(a', b') = R_θ (a, b)` and
`(c', d') = R_θ (c, d)` where `R_θ` is a rotation by θ, then
`a'c' + b'd' = ac + bd` (rotations preserve inner products,
i.e., `cos²θ + sin²θ = 1`). -/
theorem paired_coeff_product_circleTranslation (k : ℕ) (hk : 0 < k)
    (v : ℝ) (f g : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleTranslation L v f) *
      fourierCoeffReal (L := L) (2 * k - 1) (circleTranslation L v g) +
    fourierCoeffReal (L := L) (2 * k) (circleTranslation L v f) *
      fourierCoeffReal (L := L) (2 * k) (circleTranslation L v g) =
    fourierCoeffReal (L := L) (2 * k - 1) f *
      fourierCoeffReal (L := L) (2 * k - 1) g +
    fourierCoeffReal (L := L) (2 * k) f *
      fourierCoeffReal (L := L) (2 * k) g := by
  rw [fourierCoeffReal_circleTranslation_cos L k hk v f,
      fourierCoeffReal_circleTranslation_cos L k hk v g,
      fourierCoeffReal_circleTranslation_sin L k hk v f,
      fourierCoeffReal_circleTranslation_sin L k hk v g]
  -- (c·a - s·b)(c·a' - s·b') + (s·a + c·b)(s·a' + c·b')
  -- = (c²+s²)·(a·a') + (s²+c²)·(b·b') = a·a' + b·b'
  have h_cs := Real.sin_sq_add_cos_sq (2 * Real.pi * (k : ℝ) * v / L)
  set c := Real.cos (2 * Real.pi * (k : ℝ) * v / L)
  set s := Real.sin (2 * Real.pi * (k : ℝ) * v / L)
  set a := fourierCoeffReal (L := L) (2 * k - 1) f
  set b := fourierCoeffReal (L := L) (2 * k) f
  set a' := fourierCoeffReal (L := L) (2 * k - 1) g
  set b' := fourierCoeffReal (L := L) (2 * k) g
  -- After set, the goal should be purely in terms of c, s, a, b, a', b'
  linear_combination (a * a' + b * b') * h_cs

/-- **Paired product of Fourier coefficients is reflection-invariant.**

For each frequency k ≥ 1:
  `c_{2k-1}(Θf)·c_{2k-1}(Θg) + c_{2k}(Θf)·c_{2k}(Θg)`
  `= c_{2k-1}(f)·c_{2k-1}(g) + c_{2k}(f)·c_{2k}(g)`

Since cos modes are invariant and sin modes are negated, each product
`(-c)(−c') = cc'` is invariant. -/
theorem paired_coeff_product_circleReflection (k : ℕ) (hk : 0 < k)
    (f g : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleReflection L f) *
      fourierCoeffReal (L := L) (2 * k - 1) (circleReflection L g) +
    fourierCoeffReal (L := L) (2 * k) (circleReflection L f) *
      fourierCoeffReal (L := L) (2 * k) (circleReflection L g) =
    fourierCoeffReal (L := L) (2 * k - 1) f *
      fourierCoeffReal (L := L) (2 * k - 1) g +
    fourierCoeffReal (L := L) (2 * k) f *
      fourierCoeffReal (L := L) (2 * k) g := by
  rw [fourierCoeffReal_circleReflection_cos L k hk f,
      fourierCoeffReal_circleReflection_cos L k hk g,
      fourierCoeffReal_circleReflection_sin L k hk f,
      fourierCoeffReal_circleReflection_sin L k hk g]
  ring

end GaussianField

end
