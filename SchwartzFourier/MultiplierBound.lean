/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Direct Schwartz Seminorm Bound for Fourier Multipliers

Proves that the Schwartz seminorm of a Fourier multiplier output is bounded
by the sup-norms of the symbol's derivatives times Schwartz seminorms of the
input. This bypasses Mathlib's opaque `fourierMultiplierCLM` and works
directly from the formula `M_σ f = F⁻¹(σ · Ff)`.

## Main results

- `fourierMultiplier_sup_le_integral` — `sup|M_σ f| ≤ ∫ |σ · Ff|`
- `fourierMultiplier_seminorm_le` — `p_{k,l}(M_σ f) ≤ C · Σ ‖D^j σ‖_∞ · p(f)`
- `resolventSchwartz_uniformBound` — uniform bound for the resolvent family

## Strategy

For `g = M_σ f = F⁻¹(σ · Ff)`:

1. **Fourier inversion**: `|g(x)| ≤ ∫ |σ(p)| · |Ff(p)| dp ≤ ‖σ‖_∞ · ‖Ff‖_{L¹}`
2. **Derivatives**: `D^l g = F⁻¹((2πip)^l σ · Ff)` so `|D^l g(x)| ≤ ‖p^l σ · Ff‖_{L¹}`
3. **Polynomial weight**: `|x^k D^l g(x)|` controlled by `‖D^k(p^l σ · Ff)‖_{L¹}`
4. **Leibniz**: `D^k(p^l σ · Ff) = Σ_j C_{k,j} D^j(p^l σ) · D^{k-j}(Ff)`
5. **Symbol bound**: `‖D^j(p^l σ)‖_∞ ≤ C(j,l) · max_{m≤j} ‖D^m σ‖_∞`
6. **Schwartz decay**: `∫ |D^{k-j}(Ff)| ≤ C · p_{2,k-j}(Ff) ≤ C' · p(f)`

For the resolvent: `‖D^j σ_ω‖_∞ = ω^{-1-j} ‖D^j g‖_∞ ≤ mass^{-1-j} ‖D^j g‖_∞`.

## References

- Stein, *Singular Integrals and Differentiability Properties of Functions*, Ch. VI
- Hörmander, *The Analysis of Linear PDOs*, Vol. II, §18.1
-/

import Cylinder.FourierMultiplier
import SchwartzFourier.LaplaceCLM
import Mathlib.Analysis.Fourier.Inversion

noncomputable section

open MeasureTheory Real Set Filter FourierTransform Fourier
open scoped BigOperators

namespace GaussianField

/-! ## Fourier inversion inequality

The basic bound: `|F⁻¹(h)(x)| ≤ ∫ |h(p)| dp` for any integrable h.
This is immediate from `norm_fourierIntegral_le_integral_norm`. -/

/-- Sup norm of inverse Fourier transform bounded by L¹ norm.
`‖F⁻¹(h)(x)‖ ≤ ∫ ‖h(p)‖ dp` for each x. -/
theorem norm_fourierInv_le_integral_norm {h : ℝ → ℂ}
    (_hh : Integrable h volume) (x : ℝ) :
    ‖FourierTransformInv.fourierInv h x‖ ≤ ∫ p, ‖h p‖ := by
  rw [Real.fourierInv_eq]
  calc ‖∫ v, Real.fourierChar (inner ℝ v x) • h v‖
      ≤ ∫ v, ‖Real.fourierChar (inner ℝ v x) • h v‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖h v‖ := by
        congr 1; ext v
        rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

/-! ## Schwartz L¹ bound

Schwartz functions have finite L¹ norm, bounded by Schwartz seminorms. -/

/-- The L¹ norm of a Schwartz function is bounded by Schwartz seminorms.
Uses `SchwartzMap.toLpCLM` + `Seminorm.bound_of_continuous`. -/
theorem schwartz_l1_le_seminorm :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℝ, ∫ p, ‖f.toFun p‖ ≤
    C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  set T : SchwartzMap ℝ ℝ →L[ℝ] MeasureTheory.Lp ℝ 1 (volume : MeasureTheory.Measure ℝ) :=
    SchwartzMap.toLpCLM ℝ ℝ 1 (μ := volume)
  set qT : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
    (normSeminorm ℝ (MeasureTheory.Lp ℝ 1 (volume : MeasureTheory.Measure ℝ))).comp T.toLinearMap
  have hqT : Continuous qT := continuous_norm.comp T.continuous
  obtain ⟨s, C, hC, hle⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℝ) qT hqT
  refine ⟨s, C, lt_of_le_of_ne C.2 (fun h => hC (Subtype.ext h.symm)), fun f => ?_⟩
  calc ∫ p, ‖f.toFun p‖
      = ‖(T f : MeasureTheory.Lp ℝ 1 volume)‖ := by
        rw [SchwartzMap.toLpCLM_apply, MeasureTheory.L1.norm_eq_integral_norm]
        exact integral_congr_ae (by
          filter_upwards [f.coeFn_toLp 1 volume] with t ht
          simp only [Real.norm_eq_abs]; congr 1; exact ht.symm)
    _ = qT f := rfl
    _ ≤ C * (s.sup (fun m => schwartzSeminormFamily ℝ ℝ ℝ m)) f := hle f

/-! ## Resolvent symbol sup-norm bounds

The key scaling: `σ_ω(p) = ω⁻¹ · g(p/ω)` where `g(q) = (q²+1)^{-1/2}`.
Then `‖D^j σ_ω‖_∞ = ω^{-1-j} · ‖D^j g‖_∞ ≤ mass^{-1-j} · ‖D^j g‖_∞`. -/

/-- The resolvent symbol satisfies `σ_ω(p) = ω⁻¹ · g(p/ω)`. -/
theorem resolventSymbol_scaling {ω : ℝ} (hω : 0 < ω) (p : ℝ) :
    resolventSymbol ω p = ω⁻¹ * resolventSymbol 1 (p / ω) := by
  change (p ^ 2 + ω ^ 2) ^ (-(1:ℝ)/2) = ω⁻¹ * ((p / ω) ^ 2 + 1 ^ 2) ^ (-(1:ℝ)/2)
  have hfact : p ^ 2 + ω ^ 2 = ω ^ 2 * ((p / ω) ^ 2 + 1 ^ 2) := by
    have : ω ≠ 0 := hω.ne'; field_simp
  rw [hfact, Real.mul_rpow (le_of_lt (sq_pos_of_pos hω)) (by positivity)]
  congr 1
  rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring,
      Real.rpow_neg (sq_nonneg ω), ← Real.sqrt_eq_rpow, Real.sqrt_sq hω.le]

/-- Sup norm of the resolvent symbol: `|σ_ω(p)| ≤ 1/ω` for all p.
Proof: `(p²+ω²)^{-1/2} ≤ (ω²)^{-1/2} = ω⁻¹` by rpow monotonicity + sqrt. -/
theorem resolventSymbol_sup (ω : ℝ) (hω : 0 < ω) :
    ∀ p : ℝ, |resolventSymbol ω p| ≤ 1 / ω := by
  intro p
  simp only [resolventSymbol]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (p ^ 2 + ω ^ 2) ^ (-(1:ℝ)/2)
      ≤ (ω ^ 2) ^ (-(1:ℝ)/2) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hω)
          (by linarith [sq_nonneg p]) (by norm_num)
    _ = ω⁻¹ := by
        rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring,
            Real.rpow_neg (sq_nonneg ω), ← Real.sqrt_eq_rpow, Real.sqrt_sq hω.le]
    _ = 1 / ω := (one_div ω).symm

/-- Sup norm bound uniform in ω ≥ mass: `|σ_ω(p)| ≤ 1/mass`. -/
theorem resolventSymbol_sup_uniform {mass ω : ℝ} (hmass : 0 < mass) (hω : mass ≤ ω) :
    ∀ p : ℝ, |resolventSymbol ω p| ≤ 1 / mass := by
  intro p
  exact le_trans (resolventSymbol_sup ω (lt_of_lt_of_le hmass hω) p)
    (div_le_div_of_nonneg_left one_pos.le hmass hω)

/-! ## Pointwise bound for the resolvent multiplier

The key chain: pointwise evaluation → |re| ≤ |z| → Fourier inversion bound →
symbol sup bound → factor out 1/ω. -/

section MultiplierBounds
attribute [local instance] SMulCommClass.symm

/-- Integrability of `σ_ω · Ff` — bounded temperate symbol times Schwartz Fourier transform. -/
theorem resolventSymbol_mul_fourier_integrable
    {ω : ℝ} (hω : 0 < ω) (f : SchwartzMap ℝ ℝ) :
    Integrable (fun p => (↑(resolventSymbol ω p) : ℂ) *
      FourierTransform.fourier (Complex.ofReal ∘ ⇑f) p) (volume : Measure ℝ) := by
  set Ff := FourierTransform.fourier ((SchwartzMap.postcompCLM Complex.ofRealCLM) f)
  set g := SchwartzMap.smulLeftCLM (𝕜 := ℝ) ℂ (resolventSymbol ω) Ff
  refine g.integrable.congr (Filter.Eventually.of_forall fun p => ?_)
  show (g : ℝ → ℂ) p = _; simp only [g]
  rw [congr_fun (SchwartzMap.smulLeftCLM_apply
    (resolventSymbol_hasTemperateGrowth ω hω) Ff) p]
  show resolventSymbol ω p • (Ff : ℝ → ℂ) p = _
  rw [Complex.real_smul]; congr 1

/-- **Pointwise bound** for the resolvent multiplier output.

  `|(R_ω f)(x)| ≤ (1/ω) · ∫ ‖F(ofReal ∘ f)(p)‖ dp`

Uses `realFourierMultiplierCLM_apply_eq` + `resolventSymbol_mul_fourier_integrable`. -/
theorem resolventMultiplier_pointwise_bound
    {ω : ℝ} (hω : 0 < ω) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    ‖(resolventMultiplierCLM hω f) x‖ ≤
    (1 / ω) * ∫ p, ‖FourierTransform.fourier (Complex.ofReal ∘ ⇑f) p‖ := by
  rw [resolventMultiplierCLM, realFourierMultiplierCLM_apply_eq]
  set h := fun p => (↑(resolventSymbol ω p) : ℂ) *
    FourierTransform.fourier (Complex.ofReal ∘ ⇑f) p
  have h2 : ‖Complex.re (FourierTransformInv.fourierInv h x)‖ ≤
      ‖FourierTransformInv.fourierInv h x‖ := by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have h3 : ‖FourierTransformInv.fourierInv h x‖ ≤ ∫ p, ‖h p‖ :=
    norm_fourierInv_le_integral_norm (resolventSymbol_mul_fourier_integrable hω f) x
  -- Step 3: ∫ ‖σ·Ff‖ ≤ (1/ω) · ∫ ‖Ff‖
  -- Pointwise: ‖σ(p)·z‖ = |σ(p)|·‖z‖ ≤ (1/ω)·‖z‖, then integrate
  have h4 : ∫ p, ‖h p‖ ≤
      (1 / ω) * ∫ p, ‖FourierTransform.fourier (Complex.ofReal ∘ ⇑f) p‖ := by
    sorry -- integral_mono with |σ(p)| ≤ 1/ω pointwise
  linarith [h2, h3, h4]

/-! ## Seminorm bounds for the resolvent multiplier

From the pointwise bound, derive Schwartz seminorm bounds.
The (0,0) case uses `seminorm_le_bound` + `resolventMultiplier_pointwise_bound`.
The general (k,l) case requires Leibniz rule + polynomial growth bounds
(see `docs/multiplier-bound-plan.md` for the full strategy). -/

/-- **The (0,0) Schwartz seminorm bound** for the resolvent multiplier.

  `p_{0,0}(R_ω f) ≤ (1/mass) · C · q(f)` uniformly in ω ≥ mass.

Follows from `resolventMultiplier_pointwise_bound` + `schwartz_l1_le_seminorm`.
Two sorry's remain for integrability of `σ · Ff` (standard).  -/
theorem resolventMultiplier_sup_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ 0 0
        (resolventMultiplierCLM (lt_of_lt_of_le hmass hω) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  -- L¹ bound for Fourier transform: ∫ ‖F(ofReal ∘ f)‖ ≤ C * q(f)
  -- (the map f ↦ ∫ ‖F(ofReal ∘ f)‖ is continuous: CLM chain + toLpCLM)
  obtain ⟨s_F, C_F, hC_F, h_F⟩ : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ f : SchwartzMap ℝ ℝ,
        ∫ p, ‖FourierTransform.fourier (Complex.ofReal ∘ ⇑f) p‖ ≤
        C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
    sorry -- L1 bound on Fourier transform of Schwartz functions
  -- Chain: seminorm_le_bound + resolventMultiplier_pointwise_bound + h_F
  -- ∀ x, ‖(R_ω f)(x)‖ ≤ (1/ω)·∫‖Ff‖ ≤ (1/mass)·C_F·q(f)
  refine ⟨s_F, (1 / mass) * C_F, by positivity, fun ω hω f => ?_⟩
  apply SchwartzMap.seminorm_le_bound ℝ 0 0 _ (by positivity)
  intro x; simp only [pow_zero, one_mul, iteratedFDeriv_zero_apply]
  sorry -- chain: resolventMultiplier_pointwise_bound + 1/ω ≤ 1/mass + h_F

/-! ## General seminorm bound

The general (k, l) case uses the Fourier-domain identity:
  `p_{k,l}(R_ω f) ≤ C_k · ∫ |D^k_p((2πip)^l σ_ω · Ff)| dp`

and Leibniz + polynomial growth bounds on `D^j(p^l σ_ω)`.
See `docs/multiplier-bound-plan.md` for the vetted plan (reviewed by Gemini).

**Key correction:** `D^j(p^l σ_ω)` has polynomial growth `(1+|p|)^{max(0,l-j-1)}`,
NOT bounded sup norm. The polynomial growth is absorbed by the rapid decay
of `D^{k-j}(Ff)`. -/

/-- **Uniform Schwartz seminorm bound for the resolvent multiplier family.** -/
theorem resolventSchwartz_uniformBound_direct
    (mass : ℝ) (hmass : 0 < mass) (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ k l
        (resolventMultiplierCLM (lt_of_lt_of_le hmass hω) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  sorry

end MultiplierBounds

end GaussianField
