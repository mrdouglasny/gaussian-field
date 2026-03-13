/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Multipliers on Schwartz Space 𝓢(ℝ)

Axiomatizes Fourier multiplier CLMs on 𝓢(ℝ) and derives the free heat
semigroup and resolvent multiplier with their equivariance properties.

## Main definitions

- `heatSymbol t p = e^{-tp²}` — the heat kernel Fourier symbol
- `resolventSymbol ω p = (p² + ω²)^{-1/2}` — the resolvent Fourier symbol
- `freeHeatSemigroup` — CLM for the heat symbol (alias for `heatMultiplierCLM`)
- `resolventMultiplierCLM` — CLM for the resolvent symbol

## Main axioms

- `heatMultiplierCLM` — the heat kernel Fourier multiplier CLM
- `resolventMultiplierCLM` — the resolvent Fourier multiplier CLM
- `*_translation_comm` — all Fourier multipliers commute with translation
- `*_reflection_comm` — even Fourier multipliers commute with reflection

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

/-! ## Fourier multiplier CLMs (axiomatized)

Each Fourier multiplier is axiomatized as a CLM on 𝓢(ℝ) together with
its equivariance properties. The translation and reflection equivariance
follow from the structure of Fourier multipliers (universal for translation,
requires even symbol for reflection). -/

/-- **The heat kernel Fourier multiplier** on 𝓢(ℝ).

  `(e^{-tΔ} f)(x) = (4πt)^{-1/2} ∫ e^{-(x-y)²/(4t)} f(y) dy`

In Fourier space, this multiplies ℱf by `e^{-tp²}`.
Maps 𝓢(ℝ) → 𝓢(ℝ) because the Gaussian convolution kernel is Schwartz. -/
axiom heatMultiplierCLM {t : ℝ} (ht : 0 ≤ t) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ

/-- **The resolvent Fourier multiplier** on 𝓢(ℝ).

  Symbol: `(p² + ω²)^{-1/2}`. Convolution kernel: `e^{-ω|x|}/(2ω)`.

Maps 𝓢(ℝ) → 𝓢(ℝ) because the multiplier and all its derivatives are
polynomially bounded (in fact, bounded). -/
axiom resolventMultiplierCLM {ω : ℝ} (hω : 0 < ω) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ

/-! ### Equivariance axioms -/

/-- The heat multiplier commutes with translation.

  `e^{-tΔ}(T_τ f) = T_τ(e^{-tΔ} f)`

Universal for Fourier multipliers: translation by τ multiplies ℱf by
e^{-2πiτp}, which commutes with multiplication by σ(p). -/
axiom heatMultiplierCLM_translation_comm {t : ℝ} (ht : 0 ≤ t) (τ : ℝ)
    (f : SchwartzMap ℝ ℝ) :
    heatMultiplierCLM ht (schwartzTranslation τ f) =
    schwartzTranslation τ (heatMultiplierCLM ht f)

/-- The heat multiplier commutes with reflection.

  `e^{-tΔ}(Θf) = Θ(e^{-tΔ} f)`

Holds because the heat symbol is even: `e^{-t(-p)²} = e^{-tp²}`. -/
axiom heatMultiplierCLM_reflection_comm {t : ℝ} (ht : 0 ≤ t)
    (f : SchwartzMap ℝ ℝ) :
    heatMultiplierCLM ht (schwartzReflection f) =
    schwartzReflection (heatMultiplierCLM ht f)

/-- The resolvent multiplier commutes with translation.

  `M_ω(T_τ f) = T_τ(M_ω f)` -/
axiom resolventMultiplierCLM_translation_comm {ω : ℝ} (hω : 0 < ω) (τ : ℝ)
    (f : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (schwartzTranslation τ f) =
    schwartzTranslation τ (resolventMultiplierCLM hω f)

/-- The resolvent multiplier commutes with reflection.

  `M_ω(Θf) = Θ(M_ω f)`

Holds because the resolvent symbol is even: `((-p)² + ω²)^{-1/2} = (p² + ω²)^{-1/2}`. -/
axiom resolventMultiplierCLM_reflection_comm {ω : ℝ} (hω : 0 < ω)
    (f : SchwartzMap ℝ ℝ) :
    resolventMultiplierCLM hω (schwartzReflection f) =
    schwartzReflection (resolventMultiplierCLM hω f)

/-! ### Heat semigroup properties -/

/-- The heat multiplier at time 0 is the identity. -/
axiom heatMultiplierCLM_zero :
    heatMultiplierCLM (le_refl (0 : ℝ)) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ)

/-- The heat multiplier satisfies the semigroup property:
  `e^{-sΔ} ∘ e^{-tΔ} = e^{-(s+t)Δ}`.

Follows from `e^{-sp²} · e^{-tp²} = e^{-(s+t)p²}` at the symbol level. -/
axiom heatMultiplierCLM_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatMultiplierCLM hs).comp (heatMultiplierCLM ht) =
    heatMultiplierCLM (show 0 ≤ s + t from add_nonneg hs ht)

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
