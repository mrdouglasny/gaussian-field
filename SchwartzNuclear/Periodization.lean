/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Periodization: Schwartz → Smooth Circle

Defines the periodization map `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` that wraps a
Schwartz function onto a circle of period L by summing translates:

  `(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

## Main definitions

- `periodizeCLM L` — the continuous linear periodization map

## Mathematical background

For `h ∈ 𝓢(ℝ)`, the rapid decay `|h^(n)(t)| ≤ C_{N,n} (1+|t|)^{-N}`
guarantees that the sum `Σ_k h^(n)(t + kL)` converges absolutely and
uniformly on `[0, L]` for any `n` and any `N > 1`. This gives:

1. **Smoothness**: derivatives commute with the sum
2. **Periodicity**: `Σ_k h(t+L+kL) = Σ_k h(t+kL)` by reindexing
3. **Continuity**: Schwartz seminorms control circle Sobolev seminorms

## References

- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. VII
- Grafakos, *Classical Fourier Analysis*, §3.1.2
-/

import SmoothCircle.Nuclear
import SchwartzNuclear.HermiteNuclear
import Torus.Symmetry
import Cylinder.Symmetry

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Periodization CLM -/

/-- The periodization map from Schwartz space to smooth periodic functions.

`(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

The sum converges absolutely in all Sobolev norms by rapid decay of `h`.

**Proof sketch**: For any Schwartz seminorm `p_{N,n}(h) = sup_t (1+|t|)^N |h^(n)(t)|`:
- The k-th term satisfies `|h^(n)(t + kL)| ≤ p_{N,n}(h) (1+|t+kL|)^{-N}`
- For `t ∈ [0, L]`, `|t + kL| ≥ |k|L - L`, so `(1+|t+kL|)^{-N} ≤ C (1+|k|L)^{-N}`
- The sum `Σ_k (1+|k|L)^{-N}` converges for `N > 1`
- Sobolev seminorm: `‖periodize L h‖_{H^s} ≤ C_{s,L} · p_{s+2, s}(h)` -/
axiom periodizeCLM : SchwartzMap ℝ ℝ →L[ℝ] SmoothMap_Circle L ℝ

/-- Pointwise formula for periodization. -/
axiom periodizeCLM_apply (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    (periodizeCLM L h).toFun t = ∑' (k : ℤ), h (t + k * L)

/-- For compactly supported Schwartz functions with support in `[-T, T]`
and `L > 2T`, the periodization agrees with `h` on `[0, L/2]`.

This is because only the `k = 0` term is nonzero on `[0, L/2]`:
for `t ∈ [0, L/2]` and `k ≠ 0`, `|t + kL| ≥ L/2 > T`, so `h(t + kL) = 0`. -/
axiom periodizeCLM_eq_on_large_period (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL_large : L > 2 * T) :
    ∀ t ∈ Set.Icc 0 (L / 2), (periodizeCLM L h).toFun t = h t

/-! ## Intertwining with symmetries -/

/-- Periodization commutes with time translation:
`periodize L (shift_τ h) = circleTranslation L τ (periodize L h)`.

Proof: `Σ_k h(t - τ + kL) = Σ_k h((t - τ) + kL) = (periodize L h)(t - τ)`. -/
theorem periodizeCLM_comp_schwartzTranslation (τ : ℝ) (h : SchwartzMap ℝ ℝ) :
    periodizeCLM L (schwartzTranslation τ h) =
    circleTranslation L τ (periodizeCLM L h) := by
  apply SmoothMap_Circle.ext; intro t
  simp only [circleTranslation]
  show (periodizeCLM L (schwartzTranslation τ h)).toFun t =
    (periodizeCLM L h).toFun (t - τ)
  rw [periodizeCLM_apply, periodizeCLM_apply]
  congr 1; ext k
  simp [schwartzTranslation_apply]
  ring

/-- Periodization commutes with time reflection:
`periodize L (reflect h) = circleReflection L (periodize L h)`
where `reflect h(t) = h(-t)` and `circleReflection L g(t) = g(-t)`.

Proof: `Σ_k h(-t + kL) = Σ_k h(-(t - kL)) = Σ_k h(-(t + (-k)L))
= Σ_j h(-(t + jL)) = (reflect ∘ periodize L)(h)(t)`.
(Reindex `j = -k`.) -/
theorem periodizeCLM_comp_schwartzReflection (h : SchwartzMap ℝ ℝ) :
    periodizeCLM L (schwartzReflection h) =
    circleReflection L (periodizeCLM L h) := by
  apply SmoothMap_Circle.ext; intro t
  simp only [circleReflection]
  show (periodizeCLM L (schwartzReflection h)).toFun t =
    (periodizeCLM L h).toFun (-t)
  rw [periodizeCLM_apply, periodizeCLM_apply]
  -- LHS: Σ_k h(-(t + kL)), RHS: Σ_k h(-t + kL)
  -- Reindex: substitute j = -k in LHS
  rw [show (fun k : ℤ => (schwartzReflection h) (t + ↑k * L)) =
    (fun k : ℤ => h (-(t + ↑k * L))) from by ext k; simp [schwartzReflection]]
  conv_rhs => rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
  congr 1; ext k; simp; ring

end GaussianField
