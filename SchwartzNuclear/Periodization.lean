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

/-! ## Periodization: raw function and basic properties -/

/-- The periodization function: `(periodizeFun L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`. -/
def periodizeFun (h : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ := ∑' (k : ℤ), h (t + k * L)

/-- The sum `Σ_k h(t + kL)` converges absolutely for each `t` when `h` is Schwartz.

**Proof**: By `SchwartzMap.le_seminorm'` with `k = 2, n = 0`:
`|x|² · ‖h(x)‖ ≤ (seminorm ℝ 2 0) h`, so `‖h(x)‖ ≤ C/|x|²` for `|x| ≥ 1`.
For fixed `t`, only finitely many `k` have `|t + kL| < 1`; for the rest,
`‖h(t + kL)‖ ≤ C/|t + kL|² ≤ C'/(1 + |k|)²`, which is summable.

Reference: Grafakos, *Classical Fourier Analysis*, Proposition 3.1.15. -/
axiom periodize_summable (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    Summable (fun k : ℤ => h (t + k * L))

/-- The periodized function is periodic with period `L`.

**Proof**: Reindex the sum using `k ↦ k + 1`:
`Σ_k h(t + L + kL) = Σ_k h(t + (k+1)L) = Σ_j h(t + jL)`.
Uses `Equiv.tsum_eq` with the equivalence `k ↦ k + 1` on `ℤ`.

Note: `hL` is not needed; periodicity is purely algebraic (reindexing). -/
theorem periodizeFun_periodic (h : SchwartzMap ℝ ℝ) :
    Function.Periodic (periodizeFun L h) L := by
  intro t
  simp only [periodizeFun]
  -- Rewrite each term: h(t + L + kL) = h(t + (k+1)L)
  have h_rw : (fun k : ℤ => h (t + L + ↑k * L)) =
      (fun k : ℤ => h (t + (↑k + 1) * L)) :=
    funext fun k => by ring_nf
  rw [h_rw]
  -- Reindex with j = k + 1 using Equiv.tsum_eq
  rw [show (fun k : ℤ => h (t + (↑k + 1) * L)) =
    (fun k : ℤ => (fun j : ℤ => h (t + ↑j * L)) ((Equiv.addRight (1 : ℤ)) k)) from by
    ext k; simp [Equiv.addRight]]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun j : ℤ => h (t + ↑j * L))

/-- The periodized sum is smooth (`C∞`).

**Proof sketch**: Each translate `h(· + kL)` is smooth. The sum of iterated
derivatives `Σ_k h^(n)(t + kL)` converges uniformly on compact sets by
Schwartz decay (same argument as `periodize_summable` but for `h^(n)` using
`SchwartzMap.le_seminorm'` with appropriate indices). By the Weierstrass
M-test for smooth functions (`contDiff_tsum` in Mathlib), the sum is `C∞`.

More precisely, for each `n : ℕ`, the n-th derivative bound
`‖iteratedFDeriv ℝ n (h(· + kL)) x‖ = ‖iteratedDeriv n h (x + kL)‖` is bounded
by `(seminorm ℝ 0 n) h` (uniform in `k` and `x`). While this uniform bound
is not summable over `k`, a locally uniform bound using the decay
`|x + kL|² · ‖iteratedDeriv n h (x + kL)‖ ≤ (seminorm ℝ 2 n) h`
gives summability away from a finite set of `k` values, which suffices
for `contDiff_tsum` applied to truncations.

Reference: Grafakos, *Classical Fourier Analysis*, §3.1.2. -/
axiom periodize_smooth (h : SchwartzMap ℝ ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (periodizeFun L h)

/-- The periodized function as an element of `SmoothMap_Circle L ℝ`. -/
def periodizeSmoothCircle (h : SchwartzMap ℝ ℝ) : SmoothMap_Circle L ℝ :=
  ⟨periodizeFun L h, periodizeFun_periodic L h, periodize_smooth L h⟩

@[simp] theorem periodizeSmoothCircle_toFun (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    (periodizeSmoothCircle L h).toFun t = ∑' (k : ℤ), h (t + k * L) := rfl

/-! ## Linearity of periodization -/

theorem periodizeSmoothCircle_add (f g : SchwartzMap ℝ ℝ) :
    periodizeSmoothCircle L (f + g) =
    periodizeSmoothCircle L f + periodizeSmoothCircle L g := by
  apply SmoothMap_Circle.ext; intro t
  unfold periodizeSmoothCircle
  simp only [SmoothMap_Circle.add_apply, SmoothMap_Circle.coe_mk, periodizeFun]
  simp only [SchwartzMap.add_apply]
  exact (periodize_summable L f t).tsum_add (periodize_summable L g t)

theorem periodizeSmoothCircle_smul (r : ℝ) (h : SchwartzMap ℝ ℝ) :
    periodizeSmoothCircle L (r • h) = r • periodizeSmoothCircle L h := by
  apply SmoothMap_Circle.ext; intro t
  unfold periodizeSmoothCircle
  simp only [SmoothMap_Circle.smul_apply, SmoothMap_Circle.coe_mk, periodizeFun]
  rw [show (fun k : ℤ => (r • h) (t + ↑k * L)) =
    (fun k : ℤ => r • h (t + ↑k * L)) from by ext k; rfl]
  rw [tsum_const_smul'' r, smul_eq_mul]

/-- The periodization linear map (without continuity). -/
def periodizeLM : SchwartzMap ℝ ℝ →ₗ[ℝ] SmoothMap_Circle L ℝ where
  toFun := periodizeSmoothCircle L
  map_add' := periodizeSmoothCircle_add L
  map_smul' r h := by simp [periodizeSmoothCircle_smul]

/-! ## CLM continuity -/

/-- The Sobolev seminorm of the periodized function is bounded by Schwartz seminorms.

For each Sobolev order `k`, we have:
`sobolevSeminorm k (periodize h) ≤ C_{k,L} · (seminorm ℝ (k+2) k) h`

**Proof sketch**: The k-th derivative of the periodized function satisfies
`|D^k (periodize h)(t)| = |Σ_j D^k h(t + jL)| ≤ Σ_j |h^(k)(t + jL)|`.
By `SchwartzMap.le_seminorm'`, `|x|^(k+2) · |h^(k)(x)| ≤ (seminorm ℝ (k+2) k) h`,
so `|h^(k)(t + jL)| ≤ (seminorm ℝ (k+2) k) h / |t + jL|^(k+2)`.
The sum `Σ_j 1/|t + jL|^(k+2)` converges (uniformly in `t ∈ [0,L]`) since `k+2 ≥ 2 > 1`.

Reference: Stein-Weiss, Ch. VII, §2. -/
axiom periodize_sobolevSeminorm_le (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (h : SchwartzMap ℝ ℝ),
        SmoothMap_Circle.sobolevSeminorm k (periodizeSmoothCircle L h) ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℝ)) h

/-! ## Periodization CLM -/

/-- The periodization map from Schwartz space to smooth periodic functions.

`(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

Constructed as a continuous linear map using:
- `periodizeSmoothCircle` for the underlying function
- `periodize_summable` for convergence of the sum
- `periodize_smooth` for smoothness of the sum
- `periodize_sobolevSeminorm_le` for continuity (Sobolev-Schwartz bound)

The sum converges absolutely in all Sobolev norms by rapid decay of `h`. -/
def periodizeCLM : SchwartzMap ℝ ℝ →L[ℝ] SmoothMap_Circle L ℝ where
  toLinearMap := periodizeLM L
  cont := by
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ)
      SmoothMap_Circle.smoothCircle_withSeminorms
    intro i
    obtain ⟨s, C, hC, hbound⟩ := periodize_sobolevSeminorm_le L i
    refine ⟨s, ⟨C, hC⟩, fun h => ?_⟩
    simp only [Seminorm.comp_apply, NNReal.smul_def, Seminorm.smul_apply, NNReal.coe_mk]
    exact hbound h

/-- Pointwise formula for periodization. -/
theorem periodizeCLM_apply (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    (periodizeCLM L h).toFun t = ∑' (k : ℤ), h (t + k * L) := rfl

/-- For compactly supported Schwartz functions with support in `[-T, T]`
and `L > 2T`, the periodization agrees with `h` on `[0, L/2]`.

This is because only the `k = 0` term is nonzero on `[0, L/2]`:
for `t ∈ [0, L/2]` and `k ≠ 0`, `|t + kL| ≥ L/2 > T`, so `h(t + kL) = 0`. -/
theorem periodizeCLM_eq_on_large_period (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL_large : L > 2 * T) :
    ∀ t ∈ Set.Icc 0 (L / 2), (periodizeCLM L h).toFun t = h t := by
  intro t ht
  rw [periodizeCLM_apply]
  have hL_pos := hL.out
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    apply hsupp
    -- Show T < |t + k * L| for k ≠ 0
    rcases Int.lt_or_lt_of_ne hk with hk_neg | hk_pos
    · -- k ≤ -1: t + kL ≤ L/2 + (-1)·L = -L/2 < -T
      have : k ≤ (-1 : ℤ) := Int.le_sub_one_of_lt hk_neg
      have hkL : ↑k * L ≤ -L := by
        have : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast this
        nlinarith
      have : t + ↑k * L < -T := by nlinarith [ht.2]
      rw [abs_of_neg (by linarith)]
      linarith
    · -- k ≥ 1: t + kL ≥ 0 + 1·L = L > 2T > T
      have : (1 : ℤ) ≤ k := hk_pos
      have hkL : L ≤ ↑k * L := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
        nlinarith
      have htk : T < t + ↑k * L := by nlinarith [ht.1]
      rw [abs_of_pos (by linarith)]
      exact htk

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
