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

## Main theorems

- `fourierCoeffReal_circleReflection_zero` — constant mode is reflection-invariant
- `fourierCoeffReal_circleReflection_cos` — cos modes are even (reflection-invariant)
- `fourierCoeffReal_circleReflection_sin` — sin modes are odd (negated by reflection)
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

/-! ## Helper lemmas -/

omit hL in
/-- Cosine basis functions are even: `fourierBasisFun (2k-1) (-x) = fourierBasisFun (2k-1) x`. -/
private lemma fourierBasisFun_even_cos (k : ℕ) (hk : 0 < k) (x : ℝ) :
    fourierBasisFun (L := L) (2 * k - 1) (-x) = fourierBasisFun (L := L) (2 * k - 1) x := by
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 from by omega]
  simp only [fourierBasisFun, if_pos (show 2 * (k - 1) % 2 = 0 from by omega)]
  congr 1
  rw [show 2 * Real.pi * ↑(2 * (k - 1) / 2 + 1) * (-x) / L =
       -(2 * Real.pi * ↑(2 * (k - 1) / 2 + 1) * x / L) from by ring,
      Real.cos_neg]

omit hL in
/-- Sine basis functions are odd: `fourierBasisFun (2k) (-x) = -fourierBasisFun (2k) x`. -/
private lemma fourierBasisFun_odd_sin (k : ℕ) (hk : 0 < k) (x : ℝ) :
    fourierBasisFun (L := L) (2 * k) (-x) = -(fourierBasisFun (L := L) (2 * k) x) := by
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 from by omega]
  simp only [fourierBasisFun, if_neg (show ¬((2 * k - 1) % 2 = 0) from by omega)]
  rw [show 2 * Real.pi * ↑((2 * k - 1) / 2 + 1) * (-x) / L =
       -(2 * Real.pi * ↑((2 * k - 1) / 2 + 1) * x / L) from by ring,
      Real.sin_neg, mul_neg]

/-- Integral of a periodic function composed with negation equals the original. -/
private theorem integral_Icc_comp_neg_of_periodic
    (g : ℝ → ℝ) (_hg : Continuous g) (hper : Function.Periodic g L) :
    ∫ x in Set.Icc 0 L, g (-x) = ∫ x in Set.Icc 0 L, g x := by
  have hL_pos := hL.out
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL_pos.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL_pos.le]
  rw [intervalIntegral.integral_comp_neg (f := g)]
  simp only [neg_zero]
  have h := hper.intervalIntegral_add_eq (-L) 0
  simp only [neg_add_cancel, zero_add] at h
  exact h

/-- Integral of a periodic function composed with translation equals the original. -/
private theorem integral_Icc_comp_sub_of_periodic
    (g : ℝ → ℝ) (_hg : Continuous g) (hper : Function.Periodic g L) (v : ℝ) :
    ∫ x in Set.Icc 0 L, g (x - v) = ∫ x in Set.Icc 0 L, g x := by
  have hL_pos := hL.out
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL_pos.le,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL_pos.le]
  rw [intervalIntegral.integral_comp_sub_right g v]
  have h := hper.intervalIntegral_add_eq (-v) 0
  simp only [zero_add] at h
  convert h using 2 <;> ring

omit hL in
/-- Explicit cosine formula for `fourierBasisFun (2k-1)`. -/
private lemma fourierBasisFun_cos_eq (k : ℕ) (hk : 0 < k) (y : ℝ) :
    fourierBasisFun (L := L) (2 * k - 1) y =
    Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑k * y / L) := by
  rw [show (2 * k - 1 : ℕ) = 2 * (k - 1) + 1 from by omega]
  simp only [fourierBasisFun, if_pos (show 2 * (k - 1) % 2 = 0 from by omega),
    show (2 * (k - 1) / 2 + 1 : ℕ) = k from by omega]

omit hL in
/-- Explicit sine formula for `fourierBasisFun (2k)`. -/
private lemma fourierBasisFun_sin_eq (k : ℕ) (hk : 0 < k) (y : ℝ) :
    fourierBasisFun (L := L) (2 * k) y =
    Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑k * y / L) := by
  rw [show (2 * k : ℕ) = (2 * k - 1) + 1 from by omega]
  simp only [fourierBasisFun, if_neg (show ¬((2 * k - 1) % 2 = 0) from by omega),
    show ((2 * k - 1) / 2 + 1 : ℕ) = k from by omega]

omit hL in
/-- Addition formula: `basis(2k-1)(x+v) = cos(θ)·basis(2k-1)(x) - sin(θ)·basis(2k)(x)`. -/
private lemma fourierBasisFun_cos_add (k : ℕ) (hk : 0 < k) (x v : ℝ) :
    fourierBasisFun (L := L) (2 * k - 1) (x + v) =
    Real.cos (2 * Real.pi * k * v / L) * fourierBasisFun (L := L) (2 * k - 1) x -
    Real.sin (2 * Real.pi * k * v / L) * fourierBasisFun (L := L) (2 * k) x := by
  simp only [fourierBasisFun_cos_eq L k hk, fourierBasisFun_sin_eq L k hk]
  rw [show 2 * Real.pi * ↑k * (x + v) / L =
       2 * Real.pi * ↑k * x / L + 2 * Real.pi * ↑k * v / L from by ring,
      Real.cos_add]
  ring

omit hL in
/-- Addition formula: `basis(2k)(x+v) = sin(θ)·basis(2k-1)(x) + cos(θ)·basis(2k)(x)`. -/
private lemma fourierBasisFun_sin_add (k : ℕ) (hk : 0 < k) (x v : ℝ) :
    fourierBasisFun (L := L) (2 * k) (x + v) =
    Real.sin (2 * Real.pi * k * v / L) * fourierBasisFun (L := L) (2 * k - 1) x +
    Real.cos (2 * Real.pi * k * v / L) * fourierBasisFun (L := L) (2 * k) x := by
  simp only [fourierBasisFun_cos_eq L k hk, fourierBasisFun_sin_eq L k hk]
  rw [show 2 * Real.pi * ↑k * (x + v) / L =
       2 * Real.pi * ↑k * x / L + 2 * Real.pi * ↑k * v / L from by ring,
      Real.sin_add]
  ring

/-! ## Translation -/

/-- **Constant mode is translation-invariant.**

  `c₀(T_v f) = c₀(f)` -/
theorem fourierCoeffReal_circleTranslation_zero (v : ℝ)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) 0 (circleTranslation L v f) =
    fourierCoeffReal (L := L) 0 f := by
  unfold fourierCoeffReal
  have heval : ∀ x, (circleTranslation L v f) x = f (x - v) := fun _ => rfl
  simp_rw [heval]
  set g := fun x => f x * fourierBasisFun (L := L) 0 x
  have hg_per : Function.Periodic g L := fun x => by
    simp only [g]; rw [f.periodic x, fourierBasisFun_periodic 0 x]
  have hg_cont : Continuous g :=
    f.continuous.mul (fourierBasisFun_smooth 0).continuous
  have hg_sub : ∀ x, f (x - v) * fourierBasisFun (L := L) 0 x = g (x - v) := by
    intro x; simp only [g, fourierBasisFun]
  simp_rw [hg_sub]
  exact integral_Icc_comp_sub_of_periodic L g hg_cont hg_per v

/-- **Cosine mode transforms under translation by rotation.**

  `c_{2k-1}(T_v f) = cos(2πkv/L)·c_{2k-1}(f) - sin(2πkv/L)·c_{2k}(f)` -/
theorem fourierCoeffReal_circleTranslation_cos (k : ℕ) (hk : 0 < k)
    (v : ℝ) (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleTranslation L v f) =
    Real.cos (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k - 1) f -
    Real.sin (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k) f := by
  unfold fourierCoeffReal
  have heval : ∀ x, (circleTranslation L v f) x = f (x - v) := fun _ => rfl
  simp_rw [heval]
  -- Rewrite basis(2k-1)(x) = basis(2k-1)((x-v)+v)
  -- then use addition formula cos(a+b) = cos(a)cos(b) - sin(a)sin(b)
  have hdecomp : ∀ x, f (x - v) * fourierBasisFun (L := L) (2 * k - 1) x =
      Real.cos (2 * Real.pi * ↑k * v / L) * (f (x - v) * fourierBasisFun (L := L) (2 * k - 1) (x - v)) -
      Real.sin (2 * Real.pi * ↑k * v / L) * (f (x - v) * fourierBasisFun (L := L) (2 * k) (x - v)) := by
    intro x
    have h := fourierBasisFun_cos_add L k hk (x - v) v
    rw [show x - v + v = x from by ring] at h
    rw [h]; ring
  simp_rw [hdecomp]
  -- Split integral: ∫ (a*u - b*w) = a * ∫ u - b * ∫ w
  set g₁ := fun x => f (x - v) * fourierBasisFun (L := L) (2 * k - 1) (x - v)
  set g₂ := fun x => f (x - v) * fourierBasisFun (L := L) (2 * k) (x - v)
  have hg₁_int : MeasureTheory.IntegrableOn g₁ (Set.Icc 0 L) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact ((f.continuous.comp (continuous_id.sub continuous_const)).mul
      ((fourierBasisFun_smooth (2 * k - 1)).continuous.comp
        (continuous_id.sub continuous_const))).continuousOn
  have hg₂_int : MeasureTheory.IntegrableOn g₂ (Set.Icc 0 L) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact ((f.continuous.comp (continuous_id.sub continuous_const)).mul
      ((fourierBasisFun_smooth (2 * k)).continuous.comp
        (continuous_id.sub continuous_const))).continuousOn
  rw [MeasureTheory.integral_sub (hg₁_int.const_mul _) (hg₂_int.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  -- Now use periodicity: ∫ gₙ(x) dx = ∫ f(x) * basis(n)(x) dx
  -- since gₙ(x) = f(x-v) * basis(n)(x-v) = hₙ(x-v) where hₙ(y) = f(y) * basis(n)(y)
  simp only [g₁, g₂]
  set h₁ := fun y => f y * fourierBasisFun (L := L) (2 * k - 1) y
  set h₂ := fun y => f y * fourierBasisFun (L := L) (2 * k) y
  have hh₁_per : Function.Periodic h₁ L := fun x => by
    simp only [h₁]; rw [f.periodic x, fourierBasisFun_periodic (2 * k - 1) x]
  have hh₂_per : Function.Periodic h₂ L := fun x => by
    simp only [h₂]; rw [f.periodic x, fourierBasisFun_periodic (2 * k) x]
  have hh₁_cont : Continuous h₁ :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k - 1)).continuous
  have hh₂_cont : Continuous h₂ :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k)).continuous
  congr 1
  · congr 1
    exact integral_Icc_comp_sub_of_periodic L h₁ hh₁_cont hh₁_per v
  · congr 1
    exact integral_Icc_comp_sub_of_periodic L h₂ hh₂_cont hh₂_per v

/-- **Sine mode transforms under translation by rotation.**

  `c_{2k}(T_v f) = sin(2πkv/L)·c_{2k-1}(f) + cos(2πkv/L)·c_{2k}(f)` -/
theorem fourierCoeffReal_circleTranslation_sin (k : ℕ) (hk : 0 < k)
    (v : ℝ) (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k) (circleTranslation L v f) =
    Real.sin (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k - 1) f +
    Real.cos (2 * Real.pi * k * v / L) *
      fourierCoeffReal (L := L) (2 * k) f := by
  unfold fourierCoeffReal
  have heval : ∀ x, (circleTranslation L v f) x = f (x - v) := fun _ => rfl
  simp_rw [heval]
  have hdecomp : ∀ x, f (x - v) * fourierBasisFun (L := L) (2 * k) x =
      Real.sin (2 * Real.pi * ↑k * v / L) * (f (x - v) * fourierBasisFun (L := L) (2 * k - 1) (x - v)) +
      Real.cos (2 * Real.pi * ↑k * v / L) * (f (x - v) * fourierBasisFun (L := L) (2 * k) (x - v)) := by
    intro x
    have h := fourierBasisFun_sin_add L k hk (x - v) v
    rw [show x - v + v = x from by ring] at h
    rw [h]; ring
  simp_rw [hdecomp]
  set g₁ := fun x => f (x - v) * fourierBasisFun (L := L) (2 * k - 1) (x - v)
  set g₂ := fun x => f (x - v) * fourierBasisFun (L := L) (2 * k) (x - v)
  have hg₁_int : MeasureTheory.IntegrableOn g₁ (Set.Icc 0 L) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact ((f.continuous.comp (continuous_id.sub continuous_const)).mul
      ((fourierBasisFun_smooth (2 * k - 1)).continuous.comp
        (continuous_id.sub continuous_const))).continuousOn
  have hg₂_int : MeasureTheory.IntegrableOn g₂ (Set.Icc 0 L) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact ((f.continuous.comp (continuous_id.sub continuous_const)).mul
      ((fourierBasisFun_smooth (2 * k)).continuous.comp
        (continuous_id.sub continuous_const))).continuousOn
  rw [MeasureTheory.integral_add (hg₁_int.const_mul _) (hg₂_int.const_mul _),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  simp only [g₁, g₂]
  set h₁ := fun y => f y * fourierBasisFun (L := L) (2 * k - 1) y
  set h₂ := fun y => f y * fourierBasisFun (L := L) (2 * k) y
  have hh₁_per : Function.Periodic h₁ L := fun x => by
    simp only [h₁]; rw [f.periodic x, fourierBasisFun_periodic (2 * k - 1) x]
  have hh₂_per : Function.Periodic h₂ L := fun x => by
    simp only [h₂]; rw [f.periodic x, fourierBasisFun_periodic (2 * k) x]
  have hh₁_cont : Continuous h₁ :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k - 1)).continuous
  have hh₂_cont : Continuous h₂ :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k)).continuous
  congr 1
  · congr 1
    exact integral_Icc_comp_sub_of_periodic L h₁ hh₁_cont hh₁_per v
  · congr 1
    exact integral_Icc_comp_sub_of_periodic L h₂ hh₂_cont hh₂_per v

/-! ## Reflection axioms -/

/-- **Constant mode is reflection-invariant.**

  `c₀(Θf) = c₀(f)`

The constant mode is even under reflection. -/
theorem fourierCoeffReal_circleReflection_zero
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) 0 (circleReflection L f) =
    fourierCoeffReal (L := L) 0 f := by
  unfold fourierCoeffReal
  -- fourierBasisFun 0 is constant (1/√L), so the integrand product is just
  -- (f(-x) or f(x)) * (1/√L), and ∫ f(-x) = ∫ f(x) by periodicity.
  show ∫ x in Set.Icc 0 L,
      (circleReflection L f) x * fourierBasisFun (L := L) 0 x =
    ∫ x in Set.Icc 0 L, f x * fourierBasisFun (L := L) 0 x
  -- (circleReflection L f) x = f (-x) definitionally
  have heval : ∀ x, (circleReflection L f) x = f (-x) := fun _ => rfl
  simp_rw [heval]
  -- g(x) := f(x) * fourierBasisFun 0 x is L-periodic and continuous
  set g := fun x => f x * fourierBasisFun (L := L) 0 x
  have hg_per : Function.Periodic g L := fun x => by
    simp only [g]; rw [f.periodic x, fourierBasisFun_periodic 0 x]
  have hg_cont : Continuous g :=
    f.continuous.mul (fourierBasisFun_smooth 0).continuous
  -- g(-x) = f(-x) * fourierBasisFun 0 (-x) = f(-x) * fourierBasisFun 0 x
  -- since fourierBasisFun 0 is constant
  have hg_neg : ∀ x, f (-x) * fourierBasisFun (L := L) 0 x = g (-x) := by
    intro x; simp only [g, fourierBasisFun]
  simp_rw [hg_neg]
  exact integral_Icc_comp_neg_of_periodic L g hg_cont hg_per

/-- **Cosine modes are even under reflection.**

  `c_{2k-1}(Θf) = c_{2k-1}(f)`

Cosine is an even function: `cos(-x) = cos(x)`, so
`∫ f(-x) cos(2πkx/L) dx = ∫ f(y) cos(2πky/L) dy`. -/
theorem fourierCoeffReal_circleReflection_cos (k : ℕ) (hk : 0 < k)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k - 1) (circleReflection L f) =
    fourierCoeffReal (L := L) (2 * k - 1) f := by
  unfold fourierCoeffReal
  have heval : ∀ x, (circleReflection L f) x = f (-x) := fun _ => rfl
  simp_rw [heval]
  -- fourierBasisFun (2*k-1) is a cosine: √(2/L) * cos(2πk·x/L)
  -- cos is even: fourierBasisFun (2*k-1) (-x) = fourierBasisFun (2*k-1) x
  set g := fun x => f x * fourierBasisFun (L := L) (2 * k - 1) x
  have hg_per : Function.Periodic g L := fun x => by
    simp only [g]; rw [f.periodic x, fourierBasisFun_periodic (2 * k - 1) x]
  have hg_cont : Continuous g :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k - 1)).continuous
  have hg_neg : ∀ x, f (-x) * fourierBasisFun (L := L) (2 * k - 1) x = g (-x) := by
    intro x; simp only [g]
    rw [fourierBasisFun_even_cos L k hk x]
  simp_rw [hg_neg]
  exact integral_Icc_comp_neg_of_periodic L g hg_cont hg_per

/-- **Sine modes are odd under reflection.**

  `c_{2k}(Θf) = -c_{2k}(f)`

Sine is an odd function: `sin(-x) = -sin(x)`, so
`∫ f(-x) sin(2πkx/L) dx = -∫ f(y) sin(2πky/L) dy`. -/
theorem fourierCoeffReal_circleReflection_sin (k : ℕ) (hk : 0 < k)
    (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) (2 * k) (circleReflection L f) =
    -(fourierCoeffReal (L := L) (2 * k) f) := by
  unfold fourierCoeffReal
  have heval : ∀ x, (circleReflection L f) x = f (-x) := fun _ => rfl
  simp_rw [heval]
  -- fourierBasisFun (2*k) is a sine: √(2/L) * sin(2πk·x/L)
  -- sin is odd: fourierBasisFun (2*k) (-x) = -fourierBasisFun (2*k) x
  set g := fun x => f x * fourierBasisFun (L := L) (2 * k) x
  have hg_per : Function.Periodic g L := fun x => by
    simp only [g]; rw [f.periodic x, fourierBasisFun_periodic (2 * k) x]
  have hg_cont : Continuous g :=
    f.continuous.mul (fourierBasisFun_smooth (2 * k)).continuous
  have hg_neg : ∀ x, f (-x) * fourierBasisFun (L := L) (2 * k) x = -(g (-x)) := by
    intro x; simp only [g]
    rw [fourierBasisFun_odd_sin L k hk x, mul_neg, neg_neg]
  simp_rw [hg_neg, MeasureTheory.integral_neg]
  exact congrArg Neg.neg (integral_Icc_comp_neg_of_periodic L g hg_cont hg_per)

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
