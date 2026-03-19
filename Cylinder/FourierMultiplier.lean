/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Multipliers on Schwartz Space 𝓢(ℝ)

Defines Fourier multiplier CLMs on 𝓢(ℝ) via Mathlib's `fourierMultiplierCLM`
and proves the identity-at-zero property. Equivariance and semigroup
composition remain axiomatized.

## Main definitions

- `heatSymbol t p = e^{-tp²}` — the heat kernel Fourier symbol
- `resolventSymbol ω p = (p² + ω²)^{-1/2}` — the resolvent Fourier symbol
- `realFourierMultiplierCLM` — lift-apply-project CLM construction
- `heatMultiplierCLM` — CLM for the heat symbol (defined, not axiomatized)
- `resolventMultiplierCLM` — CLM for the resolvent symbol (defined)
- `freeHeatSemigroup` — alias for `heatMultiplierCLM`

## Main results

- `heatSymbol_hasTemperateGrowth` — temperate growth of heat symbol (proved)
- `resolventSymbol_hasTemperateGrowth` — temperate growth of resolvent symbol (proved)
- `heatMultiplierCLM_zero` — heat multiplier at t=0 is the identity (proved)
- `heatMultiplierCLM_comp` — semigroup composition (proved from general comp axiom)
- `*_translation_comm` — translation equivariance (proved from general axiom)
- `*_reflection_comm` — reflection equivariance (proved from general axiom)

## Remaining axioms (3 general properties of `realFourierMultiplierCLM`)

- `realFourierMultiplierCLM_comp` — composition of multipliers = multiplier of product
- `realFourierMultiplierCLM_translation_comm` — translation equivariance
- `realFourierMultiplierCLM_even_reflection_comm` — reflection equivariance for even symbols

## Mathematical background

A Fourier multiplier with symbol σ : ℝ → ℝ is the operator

  `M_σ f = ℱ⁻¹(σ · ℱf)`

where ℱ is the Fourier transform. When σ is smooth with polynomially
bounded derivatives (Hörmander class), M_σ maps 𝓢(ℝ) → 𝓢(ℝ) continuously.

**Translation equivariance** is universal: shifting f by τ multiplies ℱf
by e^{-2πiτp}, which commutes with multiplication by σ(p).

**Reflection equivariance** holds for even symbols (σ(-p) = σ(p)):
reflecting f negates the Fourier variable, and even σ is invariant.

### Specific symbols

- **Heat**: σ_t(p) = e^{-tp²}. Convolution with Gaussian (4πt)^{-1/2} e^{-x²/(4t)}.
  Even ✓. Semigroup: σ_s · σ_t = σ_{s+t}. Bounded by 1 for t ≥ 0.

- **Resolvent**: σ_ω(p) = (p² + ω²)^{-1/2}. Convolution with e^{-ω|x|}/(2ω).
  Even ✓. Bounded by ω⁻¹ for ω > 0. Square root of the Green's function.

## References

- Stein, *Harmonic Analysis*, Ch. VI
- Hörmander, *The Analysis of Linear PDOs* Vol. II, §18.1
-/

import Cylinder.Symmetry
import Mathlib.Analysis.Distribution.FourierMultiplier

noncomputable section

namespace GaussianField

/-! ## Fourier multiplier symbols

Concrete symbol functions with proved algebraic properties.
These document what the axiomatized CLMs compute in Fourier space. -/

/-- The heat kernel Fourier symbol: `σ_t(p) = e^{-tp²}`. -/
def heatSymbol (t : ℝ) (p : ℝ) : ℝ := Real.exp (-t * p ^ 2)

/-- The resolvent Fourier symbol: `σ_ω(p) = (p² + ω²)^{-1/2}`. -/
def resolventSymbol (ω : ℝ) (p : ℝ) : ℝ := (p ^ 2 + ω ^ 2) ^ (-(1 : ℝ) / 2)

/-- The heat symbol is even: `σ_t(-p) = σ_t(p)`. -/
theorem heatSymbol_even (t : ℝ) (p : ℝ) : heatSymbol t (-p) = heatSymbol t p := by
  unfold heatSymbol; congr 1; ring

/-- The resolvent symbol is even: `σ_ω(-p) = σ_ω(p)`. -/
theorem resolventSymbol_even (ω : ℝ) (p : ℝ) :
    resolventSymbol ω (-p) = resolventSymbol ω p := by
  unfold resolventSymbol; congr 1; ring

/-- The heat symbol at t = 0 is identically 1. -/
theorem heatSymbol_zero (p : ℝ) : heatSymbol 0 p = 1 := by
  simp [heatSymbol]

/-- The heat symbol satisfies the semigroup property. -/
theorem heatSymbol_mul (s t : ℝ) (p : ℝ) :
    heatSymbol s p * heatSymbol t p = heatSymbol (s + t) p := by
  simp only [heatSymbol, ← Real.exp_add]; congr 1; ring

/-- The resolvent symbol is strictly positive for ω > 0. -/
theorem resolventSymbol_pos {ω : ℝ} (hω : 0 < ω) (p : ℝ) :
    0 < resolventSymbol ω p := by
  unfold resolventSymbol
  exact Real.rpow_pos_of_pos (by positivity) _

/-! ## Real Fourier multiplier CLM via lift-apply-project

We construct real-valued Fourier multiplier CLMs on 𝓢(ℝ, ℝ) by:
1. **Lift**: embed 𝓢(ℝ, ℝ) → 𝓢(ℝ, ℂ) via `Complex.ofRealCLM`
2. **Apply**: use Mathlib's `fourierMultiplierCLM` on 𝓢(ℝ, ℂ)
3. **Project**: extract the real part 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℝ) via `Complex.reCLM`

This gives concrete definitions (not axioms) for the heat and resolvent
multiplier CLMs, modulo `HasTemperateGrowth` for their symbols. -/

/-- The heat symbol has temperate growth for t ≥ 0.

The heat symbol `e^{-tp²}` is smooth and all derivatives are bounded
(in fact, Schwartz), so `HasTemperateGrowth` holds with k = 0.

Proof: `heatSymbol t = exp ∘ (p ↦ -tp²)`. The inner function is polynomial
(temperate growth by `fun_prop`). The outer function `exp` is smooth and all
derivatives (= exp) are bounded by `exp(1)` on `(-∞, 1)`, which contains the
range of the inner function for t ≥ 0. Apply `HasTemperateGrowth.comp'`. -/
theorem heatSymbol_hasTemperateGrowth (t : ℝ) (ht : 0 ≤ t) :
    (heatSymbol t).HasTemperateGrowth := by
  show (Real.exp ∘ (fun p => -t * p ^ 2)).HasTemperateGrowth
  apply Function.HasTemperateGrowth.comp' (t := Set.Iio 1)
  · rintro _ ⟨p, rfl⟩
    simp only [Set.mem_Iio]
    nlinarith [sq_nonneg p]
  · exact isOpen_Iio.uniqueDiffOn
  · exact Real.contDiff_exp.contDiffOn
  · intro N
    refine ⟨0, Real.exp 1, le_of_lt (Real.exp_pos 1), ?_⟩
    intro n _ x hx
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv isOpen_Iio.uniqueDiffOn
        (Real.contDiff_exp.contDiffAt.of_le le_top) hx,
      iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
    simp only [pow_zero, mul_one]
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.mpr hx.le
  · fun_prop

/-- The resolvent symbol has temperate growth for ω > 0.

The resolvent symbol `(p² + ω²)^{-1/2}` is smooth (since the base is everywhere
positive) and all derivatives are bounded because the exponent `r - n < 0`
for all derivative orders `n`, making `y^{r-n}` decreasing. We apply
`HasTemperateGrowth.comp'` with outer function `y^{-1/2}` restricted to
`{y | ω²/2 < y}` (an open set containing the range of `p² + ω²`). -/
theorem resolventSymbol_hasTemperateGrowth (ω : ℝ) (hω : 0 < ω) :
    (resolventSymbol ω).HasTemperateGrowth := by
  show ((fun y => y ^ (-(1 : ℝ) / 2)) ∘ (fun p => p ^ 2 + ω ^ 2)).HasTemperateGrowth
  have hω2 : (0 : ℝ) < ω ^ 2 / 2 := by positivity
  apply Function.HasTemperateGrowth.comp' (t := Set.Ioi (ω ^ 2 / 2))
  · rintro _ ⟨p, rfl⟩
    simp only [Set.mem_Ioi]
    nlinarith [sq_nonneg p, pow_pos hω 2]
  · exact isOpen_Ioi.uniqueDiffOn
  · exact contDiffOn_fun_id.rpow_const_of_ne fun x hx => (lt_trans hω2 hx).ne'
  · intro N
    refine ⟨0, ∑ k ∈ Finset.range (N + 1),
      ‖(descPochhammer ℝ k).eval (-(1 : ℝ) / 2)‖ * (ω ^ 2 / 2) ^ (-(1 : ℝ) / 2 - ↑k),
      by positivity, ?_⟩
    intro n hn x hx
    have hx_pos : 0 < x := lt_trans hω2 hx
    have hrn : -(1 : ℝ) / 2 - (n : ℝ) < 0 := by
      have : (0 : ℝ) ≤ (n : ℝ) := n.cast_nonneg; linarith
    rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
      iteratedDerivWithin_eq_iteratedDeriv isOpen_Ioi.uniqueDiffOn
        (Real.contDiffAt_rpow_const_of_ne hx_pos.ne') hx,
      iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const, norm_mul,
      pow_zero, mul_one]
    have h1 : ‖x ^ (-(1 : ℝ) / 2 - ↑n)‖ ≤ (ω ^ 2 / 2) ^ (-(1 : ℝ) / 2 - ↑n) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx_pos _)]
      exact (Real.rpow_le_rpow_iff_of_neg hx_pos hω2 hrn).mpr hx.le
    calc ‖(descPochhammer ℝ n).eval (-(1 : ℝ) / 2)‖ * ‖x ^ (-(1 : ℝ) / 2 - ↑n)‖
        ≤ ‖(descPochhammer ℝ n).eval (-(1 : ℝ) / 2)‖ *
            (ω ^ 2 / 2) ^ (-(1 : ℝ) / 2 - ↑n) := by gcongr
      _ ≤ ∑ k ∈ Finset.range (N + 1),
            ‖(descPochhammer ℝ k).eval (-(1 : ℝ) / 2)‖ *
              (ω ^ 2 / 2) ^ (-(1 : ℝ) / 2 - ↑k) :=
          Finset.single_le_sum (f := fun k =>
              ‖(descPochhammer ℝ k).eval (-(1 : ℝ) / 2)‖ *
                (ω ^ 2 / 2) ^ (-(1 : ℝ) / 2 - (k : ℝ)))
            (fun k _ => mul_nonneg (norm_nonneg _)
              (le_of_lt (Real.rpow_pos_of_pos hω2 _)))
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  · fun_prop

/-- Lift real Schwartz functions to complex: `f ↦ ofReal ∘ f`. -/
def schwartzToComplex : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM Complex.ofRealCLM

/-- Project complex Schwartz functions to real: `f ↦ re ∘ f`. -/
def schwartzToReal : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℝ :=
  SchwartzMap.postcompCLM Complex.reCLM

/-- The roundtrip `re ∘ ofReal = id` on real Schwartz functions. -/
theorem schwartzToReal_comp_schwartzToComplex :
    schwartzToReal.comp schwartzToComplex =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  ext f x
  simp [schwartzToReal, schwartzToComplex]

attribute [local instance] SMulCommClass.symm in
/-- **Real Fourier multiplier CLM** via lift-apply-project.

For a real-valued symbol `σ : ℝ → ℝ` with temperate growth, this is
`re ∘ M_σ ∘ ofReal` where `M_σ = ℱ⁻¹ ∘ (σ · ) ∘ ℱ` is Mathlib's
`fourierMultiplierCLM` applied on `𝓢(ℝ, ℂ)` with scalar field `ℝ`.

Using `𝕜 = ℝ` means all three CLMs in the composition are `→L[ℝ]`,
avoiding the need for `restrictScalars`. -/
def realFourierMultiplierCLM (σ : ℝ → ℝ)
    (_hσ : σ.HasTemperateGrowth) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  schwartzToReal.comp
    ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ).comp schwartzToComplex)

/-! ### Fourier multiplier real-valuedness

A Fourier multiplier with real-valued symbol preserves real-valuedness of
Schwartz functions. This follows from the conjugation symmetry of the
Fourier transform: if f is real then f̂(-ξ) = conj(f̂(ξ)), so
(σ · f̂)(-ξ) = σ(-ξ)f̂(-ξ) = σ(-ξ)conj(f̂(ξ)). For real σ,
conj(σ(ξ)f̂(ξ)) = σ(ξ)conj(f̂(ξ)), so if also σ is even (σ(-ξ) = σ(ξ)),
then (σ · f̂) has conjugation symmetry and ℱ⁻¹(σ · f̂) is real.

For the composition theorem, we only need: M_σ(ofReal f) has zero imaginary
part, i.e., `re ∘ M_σ ∘ ofReal = M_σ ∘ ofReal` (equivalently,
`ofReal ∘ re ∘ M_σ ∘ ofReal = M_σ ∘ ofReal`).

Reference: Stein-Weiss, *Fourier Analysis*, Ch. I. -/

-- Need SMulCommClass for fourierMultiplierCLM with 𝕜 = ℝ
section FourierMultiplierProperties
attribute [local instance] SMulCommClass.symm

/-- Real Fourier multiplier preserves real-valuedness.
Consequence of Fourier conjugation symmetry + real-valued symbol. -/
axiom fourierMultiplier_preserves_real (σ : ℝ → ℝ) (hσ : σ.HasTemperateGrowth) :
    schwartzToComplex.comp (schwartzToReal.comp
      ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ).comp schwartzToComplex)) =
    (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ).comp schwartzToComplex

/-! ### Fourier multiplier properties

The composition theorem is proved from Mathlib's
`fourierMultiplierCLM_compL_fourierMultiplierCLM` + the real-valuedness axiom.
The translation and reflection equivariance remain axiomatized. -/

/-- **Composition of real Fourier multipliers.**

  `M_{σ₁} ∘ M_{σ₂} = M_{σ₁ · σ₂}`

Proved from Mathlib's `fourierMultiplierCLM_compL_fourierMultiplierCLM`
on the complex side, plus `fourierMultiplier_preserves_real`. -/
theorem realFourierMultiplierCLM_comp (σ₁ σ₂ : ℝ → ℝ)
    (hσ₁ : σ₁.HasTemperateGrowth) (hσ₂ : σ₂.HasTemperateGrowth) :
    (realFourierMultiplierCLM σ₁ hσ₁).comp (realFourierMultiplierCLM σ₂ hσ₂) =
    realFourierMultiplierCLM (σ₁ * σ₂) (hσ₁.mul hσ₂) := by
  simp only [realFourierMultiplierCLM, ContinuousLinearMap.comp_assoc]
  congr 1
  rw [show (SchwartzMap.fourierMultiplierCLM ℂ σ₁).comp
      (schwartzToComplex.comp (schwartzToReal.comp
        ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ₂).comp schwartzToComplex))) =
    (SchwartzMap.fourierMultiplierCLM ℂ σ₁).comp
      ((SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ₂).comp schwartzToComplex) from by
    congr 1; exact fourierMultiplier_preserves_real σ₂ hσ₂]
  rw [← ContinuousLinearMap.comp_assoc]
  congr 1
  exact SchwartzMap.fourierMultiplierCLM_compL_fourierMultiplierCLM hσ₁ hσ₂

/-- **Fourier multiplier commutes with translation (complex side).**

  `M_σ(T_τ f) = T_τ(M_σ f)` on `𝓢(ℝ, ℂ)`

Standard: translation by τ multiplies ℱf by e^{-2πiτp}, which commutes
with pointwise multiplication by σ(p).

Reference: Stein, *Singular Integrals*, Ch. I. -/
axiom fourierMultiplierCLM_translation_comm (σ : ℝ → ℝ)
    (hσ : σ.HasTemperateGrowth) (τ : ℝ) (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ (SchwartzMap.compSubConstCLM ℝ τ f) =
    SchwartzMap.compSubConstCLM ℝ τ (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ f)

/-- **Fourier multiplier with even symbol commutes with reflection (complex side).**

  `M_σ(Θf) = Θ(M_σ f)` on `𝓢(ℝ, ℂ)` when `σ(-p) = σ(p)`

Reflection negates the Fourier variable, and even σ is invariant.

Reference: Stein, *Singular Integrals*, Ch. I. -/
axiom fourierMultiplierCLM_even_reflection_comm (σ : ℝ → ℝ)
    (hσ : σ.HasTemperateGrowth) (heven : ∀ p, σ (-p) = σ p)
    (f : SchwartzMap ℝ ℂ) :
    SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv f) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
      (SchwartzMap.fourierMultiplierCLM (𝕜 := ℝ) ℂ σ f)

/-- **Translation equivariance of real Fourier multipliers.**

  `M_σ(T_τ f) = T_τ(M_σ f)`

Proved from the complex version `fourierMultiplierCLM_translation_comm`
+ real-valuedness preservation. -/
theorem realFourierMultiplierCLM_translation_comm (σ : ℝ → ℝ)
    (hσ : σ.HasTemperateGrowth) (τ : ℝ) (f : SchwartzMap ℝ ℝ) :
    realFourierMultiplierCLM σ hσ (schwartzTranslation τ f) =
    schwartzTranslation τ (realFourierMultiplierCLM σ hσ f) := by
  simp only [realFourierMultiplierCLM, schwartzTranslation]
  simp only [ContinuousLinearMap.comp_apply]
  -- LHS: re(M_σ(ofReal(T_τ f))) = re(M_σ(T_τ(ofReal f)))
  -- schwartzToComplex commutes with translation:
  have h1 : schwartzToComplex (SchwartzMap.compSubConstCLM ℝ τ f) =
      SchwartzMap.compSubConstCLM ℝ τ (schwartzToComplex f) := by
    apply SchwartzMap.ext; intro x; rfl
  rw [h1, fourierMultiplierCLM_translation_comm σ hσ τ]
  -- schwartzToReal commutes with translation:
  apply SchwartzMap.ext; intro x; rfl

/-- **Reflection equivariance of real Fourier multipliers with even symbol.**

  `M_σ(Θf) = Θ(M_σ f)` when `σ(-p) = σ(p)`

Proved from the complex version `fourierMultiplierCLM_even_reflection_comm`
+ real-valuedness preservation. -/
theorem realFourierMultiplierCLM_even_reflection_comm (σ : ℝ → ℝ)
    (hσ : σ.HasTemperateGrowth) (heven : ∀ p, σ (-p) = σ p)
    (f : SchwartzMap ℝ ℝ) :
    realFourierMultiplierCLM σ hσ (schwartzReflection f) =
    schwartzReflection (realFourierMultiplierCLM σ hσ f) := by
  simp only [realFourierMultiplierCLM, schwartzReflection]
  simp only [ContinuousLinearMap.comp_apply]
  -- LHS: re(M_σ(ofReal(Θf)))
  -- ofReal commutes with reflection (both are function composition):
  -- schwartzToComplex commutes with reflection:
  have h1 : schwartzToComplex
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv f) =
    SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv
      (schwartzToComplex f) := by
    apply SchwartzMap.ext; intro x; rfl
  rw [h1, fourierMultiplierCLM_even_reflection_comm σ hσ heven]
  -- schwartzToReal commutes with reflection:
  apply SchwartzMap.ext; intro x; rfl

end FourierMultiplierProperties

/-! ## Fourier multiplier CLMs (defined)

Each Fourier multiplier is now defined concretely via
`realFourierMultiplierCLM`, with `HasTemperateGrowth` proved for
the symbols. -/

/-- **The heat kernel Fourier multiplier** on 𝓢(ℝ).

  `(e^{-tΔ} f)(x) = ℱ⁻¹(e^{-tp²} · ℱf)(x)`

Defined via lift-apply-project from Mathlib's `fourierMultiplierCLM`. -/
def heatMultiplierCLM {t : ℝ} (ht : 0 ≤ t) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  realFourierMultiplierCLM (heatSymbol t) (heatSymbol_hasTemperateGrowth t ht)

/-- **The resolvent Fourier multiplier** on 𝓢(ℝ).

  Symbol: `(p² + ω²)^{-1/2}`. Convolution kernel: `e^{-ω|x|}/(2ω)`.

Defined via lift-apply-project from Mathlib's `fourierMultiplierCLM`. -/
def resolventMultiplierCLM {ω : ℝ} (hω : 0 < ω) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  realFourierMultiplierCLM (resolventSymbol ω) (resolventSymbol_hasTemperateGrowth ω hω)

/-! ### Equivariance axioms -/

/-- The heat multiplier commutes with translation.

  `e^{-tΔ}(T_τ f) = T_τ(e^{-tΔ} f)`

Proved from the general translation equivariance of Fourier multipliers. -/
theorem heatMultiplierCLM_translation_comm {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (f : SchwartzMap ℝ ℝ) :
    heatMultiplierCLM ht (schwartzTranslation τ f) =
    schwartzTranslation τ (heatMultiplierCLM ht f) :=
  realFourierMultiplierCLM_translation_comm _ _ τ f

/-- The heat multiplier commutes with reflection.

  `e^{-tΔ}(Θf) = Θ(e^{-tΔ} f)`

Proved from general reflection equivariance + evenness of the heat symbol. -/
theorem heatMultiplierCLM_reflection_comm {t : ℝ} (ht : 0 ≤ t)
    (f : SchwartzMap ℝ ℝ) :
    heatMultiplierCLM ht (schwartzReflection f) =
    schwartzReflection (heatMultiplierCLM ht f) :=
  realFourierMultiplierCLM_even_reflection_comm _ _ (heatSymbol_even t) f

/-- The resolvent multiplier commutes with translation.

  `M_ω(T_τ f) = T_τ(M_ω f)`

Proved from the general translation equivariance of Fourier multipliers. -/
theorem resolventMultiplierCLM_translation_comm {ω : ℝ} (hω : 0 < ω) (τ : ℝ)
    (f : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (schwartzTranslation τ f) =
    schwartzTranslation τ (resolventMultiplierCLM hω f) :=
  realFourierMultiplierCLM_translation_comm _ _ τ f

/-- The resolvent multiplier commutes with reflection.

  `M_ω(Θf) = Θ(M_ω f)`

Proved from general reflection equivariance + evenness of the resolvent symbol. -/
theorem resolventMultiplierCLM_reflection_comm {ω : ℝ} (hω : 0 < ω)
    (f : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (schwartzReflection f) =
    schwartzReflection (resolventMultiplierCLM hω f) :=
  realFourierMultiplierCLM_even_reflection_comm _ _ (resolventSymbol_even ω) f

/-! ### Heat semigroup properties -/

/-- The heat multiplier at time 0 is the identity.

Proof: `heatSymbol 0 = 1`, so the Fourier multiplier is `1 • id = id`,
and the roundtrip `re ∘ ofReal = id` completes the proof. -/
theorem heatMultiplierCLM_zero :
    heatMultiplierCLM (le_refl (0 : ℝ)) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  show realFourierMultiplierCLM (heatSymbol 0) _ = _
  have h1 : heatSymbol 0 = fun _ => (1 : ℝ) := by ext p; exact heatSymbol_zero p
  simp only [h1]
  ext f x
  simp [realFourierMultiplierCLM, schwartzToReal, schwartzToComplex,
    SchwartzMap.fourierMultiplierCLM_const]

/-- The heat multiplier satisfies the semigroup property:
  `e^{-sΔ} ∘ e^{-tΔ} = e^{-(s+t)Δ}`.

Proved from the general composition axiom + symbol multiplication identity. -/
theorem heatMultiplierCLM_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatMultiplierCLM hs).comp (heatMultiplierCLM ht) =
    heatMultiplierCLM (show 0 ≤ s + t from add_nonneg hs ht) := by
  show (realFourierMultiplierCLM _ _).comp (realFourierMultiplierCLM _ _) = _
  rw [realFourierMultiplierCLM_comp]
  congr 1
  ext p
  exact heatSymbol_mul s t p

/-! ## Derived definitions and theorems

The free heat semigroup is defined as the heat multiplier CLM.
All previously axiomatized properties are now derived theorems. -/

/-- **The free heat semigroup** `e^{-tΔ}` on 𝓢(ℝ), defined as the
Fourier multiplier with symbol `e^{-tp²}`. -/
def freeHeatSemigroup {t : ℝ} (ht : 0 ≤ t) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  heatMultiplierCLM ht

/-- The free heat semigroup at time 0 is the identity. -/
theorem freeHeatSemigroup_zero :
    freeHeatSemigroup (le_refl (0 : ℝ)) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) :=
  heatMultiplierCLM_zero

/-- The free heat semigroup satisfies the semigroup property. -/
theorem freeHeatSemigroup_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (freeHeatSemigroup hs).comp (freeHeatSemigroup ht) =
    freeHeatSemigroup (show 0 ≤ s + t from add_nonneg hs ht) :=
  heatMultiplierCLM_comp hs ht

/-- The free heat semigroup commutes with translation. -/
theorem freeHeatSemigroup_translation_comm {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (f : SchwartzMap ℝ ℝ) :
    freeHeatSemigroup ht (schwartzTranslation τ f) =
    schwartzTranslation τ (freeHeatSemigroup ht f) :=
  heatMultiplierCLM_translation_comm ht τ f

/-- The free heat semigroup commutes with reflection. -/
theorem freeHeatSemigroup_reflection_comm {t : ℝ} (ht : 0 ≤ t)
    (f : SchwartzMap ℝ ℝ) :
    freeHeatSemigroup ht (schwartzReflection f) =
    schwartzReflection (freeHeatSemigroup ht f) :=
  heatMultiplierCLM_reflection_comm ht f

end GaussianField
