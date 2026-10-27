/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Resolvent Schwartz Seminorm Bound

Proves that the Schwartz seminorm `p_{k,l}(R_ω f)` of the resolvent multiplier
`R_ω = M_{(p²+ω²)^{-1/2}}` is bounded uniformly in `ω ≥ mass > 0`.

## Main results

- `schwartz_seminorm_smulLeftCLM_le` — σ-uniform Leibniz bound for `σ • g` on Schwartz space
- `fourierMultiplier_schwartz_bound` — `p_{k,l}(M_σ f) ≤ C' · q(f)` uniformly over symbols
  whose first `deriv_order(k, l)` derivatives are bounded by `B (1 + |p|)^N`
- `resolventSchwartz_uniformBound` — `p_{k,l}(R_ω f) ≤ C · q(f)` uniformly in ω ≥ mass

## Proof strategy

1. `M_σ = re ∘ 𝓕⁻ ∘ (σ ·) ∘ 𝓕 ∘ ofReal`: the two outer maps are fixed CLMs, bounded by
   finitely many seminorms (`Seminorm.bound_of_continuous`); multiplication by `σ` is bounded
   by the Leibniz rule with constants depending only on the symbol bounds.
2. The scaling identity `σ_ω(p) = ω⁻¹ σ₁(ω⁻¹ p)` gives derivative bounds on `σ_ω`, uniform
   in `ω ≥ mass` (`resolventSymbol_uniform_deriv_bound`).
3. Combining 1 and 2 gives `resolventSchwartz_uniformBound`.

The quotient symbol `τ_ω = σ_ω / σ_mass` and the factorization `σ_mass · τ_ω = σ_ω`
are also recorded below.

## References

- Stein, *Singular Integrals*, Ch. VI (Fourier multiplier seminorm bounds)
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/
module

public import Cylinder.FourierMultiplier

@[expose] public section

noncomputable section

namespace GaussianField

/-! ## Resolvent symbol monotonicity

The resolvent symbol is monotone decreasing in ω. (Its derivatives are not: see the note in
the next section.) -/

/-- The resolvent symbol is monotone decreasing in ω for ω > 0.

  `(p² + ω₁²)^{-1/2} ≤ (p² + ω₂²)^{-1/2}` when `ω₁ ≥ ω₂ > 0` -/
theorem resolventSymbol_antitone (p : ℝ) {ω₁ ω₂ : ℝ}
    (hω₂ : 0 < ω₂) (hle : ω₂ ≤ ω₁) :
    resolventSymbol ω₁ p ≤ resolventSymbol ω₂ p := by
  unfold resolventSymbol
  apply Real.rpow_le_rpow_of_nonpos
  · positivity
  · have : p ^ 2 + ω₂ ^ 2 ≤ p ^ 2 + ω₁ ^ 2 := by nlinarith
    exact_mod_cast this
  · norm_num

/-! ## Quotient symbol

The quotient symbol

  `τ_ω(p) = σ_ω(p) / σ_mass(p) = √((p² + mass²) / (p² + ω²))`

satisfies `0 < τ_ω(p) ≤ 1` for all p ∈ ℝ and ω ≥ mass, is even, and factorizes
`σ_mass · τ_ω = σ_ω`, i.e. `R_ω = R_mass ∘ M_{τ_ω}` (proved below).

NOTE: comparing derivatives of σ_ω and σ_mass pointwise fails because ∂ⁿσ_ω(p) involves
polynomial numerators in p (e.g., ∂σ_ω/∂p = -p(p²+ω²)^{-3/2}), which are NOT monotone in ω.
The uniform bound below instead uses the scaling identity `σ_ω(p) = ω⁻¹ σ₁(ω⁻¹ p)`. -/

/-- The quotient symbol τ_ω(p) = √((p² + mass²) / (p² + ω²)).

This is the ratio `σ_ω / σ_mass` of resolvent symbols.
Satisfies `0 < τ_ω(p) ≤ 1` for `ω ≥ mass > 0`. -/
def resolventQuotientSymbol (mass ω : ℝ) (p : ℝ) : ℝ :=
  Real.sqrt ((p ^ 2 + mass ^ 2) / (p ^ 2 + ω ^ 2))

/-- The quotient symbol is bounded by 1 for ω ≥ mass. -/
theorem resolventQuotientSymbol_le_one {mass ω : ℝ}
    (hmass : 0 < mass) (hω : mass ≤ ω) (p : ℝ) :
    resolventQuotientSymbol mass ω p ≤ 1 := by
  unfold resolventQuotientSymbol
  rw [Real.sqrt_le_one]
  rw [div_le_one (by nlinarith [sq_nonneg p])]
  nlinarith [sq_nonneg p, sq_nonneg mass, sq_nonneg ω]

/-- The quotient symbol is strictly positive for mass > 0. -/
theorem resolventQuotientSymbol_pos {mass ω : ℝ}
    (hmass : 0 < mass) (_hω : mass ≤ ω) (p : ℝ) :
    0 < resolventQuotientSymbol mass ω p := by
  unfold resolventQuotientSymbol
  apply Real.sqrt_pos_of_pos
  exact div_pos (by nlinarith [sq_nonneg p]) (by nlinarith [sq_nonneg p])

/-! ## Factorization identity

The product of the resolvent symbol at mass with the quotient symbol
equals the resolvent symbol at ω. -/

/-- `σ_mass · τ_ω = σ_ω`: the resolvent factorizes through the quotient symbol. -/
theorem resolventSymbol_mul_quotient {mass ω : ℝ} (hmass : 0 < mass) (hω : mass ≤ ω) (p : ℝ) :
    resolventSymbol mass p * resolventQuotientSymbol mass ω p = resolventSymbol ω p := by
  -- (p²+m²)^{-1/2} · √((p²+m²)/(p²+ω²)) = (p²+ω²)^{-1/2}
  -- Proof: (p²+m²)^{-1/2} · (p²+m²)^{1/2} · (p²+ω²)^{-1/2} cancel the (p²+m²) factors.
  unfold resolventSymbol resolventQuotientSymbol
  have hm : 0 < p ^ 2 + mass ^ 2 := by nlinarith [sq_nonneg p]
  have hw : 0 < p ^ 2 + ω ^ 2 := by nlinarith [sq_nonneg p]
  rw [Real.sqrt_eq_rpow, Real.div_rpow hm.le hw.le]
  rw [show (1 : ℝ) / 2 = -(-(1 : ℝ) / 2) from by norm_num]
  rw [Real.rpow_neg hm.le]
  have h1 := Real.rpow_pos_of_pos hm (-(1 : ℝ) / 2)
  field_simp
  rw [Real.rpow_neg hw.le, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hw _))]

/-- The quotient symbol is even: `τ_ω(-p) = τ_ω(p)`. -/
theorem resolventQuotientSymbol_even (mass ω : ℝ) (p : ℝ) :
    resolventQuotientSymbol mass ω (-p) = resolventQuotientSymbol mass ω p := by
  unfold resolventQuotientSymbol; ring_nf

/-! ## Fourier multiplier seminorm bounds on S(ℝ), uniform over a symbol class

A smooth symbol with polynomially bounded derivatives gives a continuous operator on S(ℝ),
with seminorm bounds depending only on the derivative-bound parameters `(B, N)` and on how
many symbol derivatives are controlled. The number of controlled derivatives must be allowed
to depend on the target seminorm `(k, l)`: see `fourierMultiplier_schwartz_bound`.

Reference: Stein, *Singular Integrals*, Ch. VI. -/

/-- **σ-uniform Leibniz bound for multiplication by a smooth real function.**

If `‖D^m σ(x)‖ ≤ B (1 + ‖x‖)^L` for all `m ≤ n`, then for every Schwartz `g`,
`p_{k,n}(σ • g) ≤ 2^n · B · 2^(L+k) · sup_{(a,b) ≤ (L+k,n)} p_{a,b}(g)`. The constant depends
on `σ` only through `(B, L)`. -/
theorem schwartz_seminorm_smulLeftCLM_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {σ : E → ℝ} (hσ : σ.HasTemperateGrowth) {n L : ℕ} {B : ℝ}
    (hB : ∀ m ≤ n, ∀ x : E, ‖iteratedFDeriv ℝ m σ x‖ ≤ B * (1 + ‖x‖) ^ L)
    (k : ℕ) (g : SchwartzMap E F) :
    SchwartzMap.seminorm ℝ k n (SchwartzMap.smulLeftCLM F σ g) ≤
      2 ^ n * B * 2 ^ (L + k) *
        (Finset.Iic (L + k, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g := by
  have hB0 : 0 ≤ B := by
    have h := hB 0 (Nat.zero_le n) 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  set S := (Finset.Iic (L + k, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) g
  have hS : 0 ≤ S := apply_nonneg _ _
  refine SchwartzMap.seminorm_le_bound ℝ k n _ (by positivity) fun x => ?_
  rw [SchwartzMap.smulLeftCLM_apply hσ]
  have hLeib := norm_iteratedFDeriv_smul_le hσ.1 (g.smooth ⊤) x (n := n) (mod_cast le_top)
  have hx : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := by gcongr; linarith
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => σ y • g y) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i σ x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ := by gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (B * 2 ^ (L + k) * S) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have h1 := hB i hi' x
        have h2 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (L + k, n))
          (k := L + k) (n := n - i) le_rfl (Nat.sub_le n i) g x
        calc ‖x‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i σ x‖ *
              ‖iteratedFDeriv ℝ (n - i) g x‖)
            ≤ (1 + ‖x‖) ^ k * ((n.choose i : ℝ) * (B * (1 + ‖x‖) ^ L) *
              ‖iteratedFDeriv ℝ (n - i) g x‖) := by gcongr
          _ = (n.choose i : ℝ) * B * ((1 + ‖x‖) ^ (L + k) *
              ‖iteratedFDeriv ℝ (n - i) g x‖) := by ring
          _ ≤ (n.choose i : ℝ) * B * (2 ^ (L + k) * S) := by gcongr
          _ = (n.choose i : ℝ) * (B * 2 ^ (L + k) * S) := by ring
    _ = 2 ^ n * B * 2 ^ (L + k) * S := by
        rw [← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
          exact_mod_cast Nat.sum_range_choose n
        rw [this]; ring

section MultiplierSchwartzBound
attribute [local instance] SMulCommClass.symm

/-- **Schwartz seminorm bound for real Fourier multipliers, uniform over a symbol class.**

For every target seminorm `(k, l)` there is a number `deriv_order` of symbol derivatives such
that, for all `B, N`, one finite set `s` of seminorms and one constant `C' > 0` work for every
symbol `σ` with `‖D^m σ(p)‖ ≤ B (1 + |p|)^N` for `m ≤ deriv_order`:

  `p_{k,l}(M_σ f) ≤ C' · (s.sup p)(f)`.

Proof: `M_σ = re ∘ 𝓕⁻ ∘ (σ ·) ∘ 𝓕 ∘ ofReal`. The outer map `re ∘ 𝓕⁻` and the inner map
`𝓕 ∘ ofReal` are fixed continuous linear maps, hence bounded by finitely many seminorms
(`Seminorm.bound_of_continuous`); `deriv_order` is the largest derivative index among the
seminorms bounding `p_{k,l} ∘ re ∘ 𝓕⁻`. Multiplication by `σ` is bounded σ-uniformly by the
Leibniz rule (`schwartz_seminorm_smulLeftCLM_le`).

This replaces an axiom that took `deriv_order` as an arbitrary input. That version is false:
for `deriv_order = 0`, `k = 1`, `l = 0`, `B = 1`, `N = 0`, the symbols `σₙ(p) = cos(2πnp)`
are admissible, but `M_{σₙ} f = (f(· + n) + f(· - n)) / 2`, so
`p_{1,0}(M_{σₙ} f) ≥ n · |f(2n) + f(0)| / 2 → ∞` whenever `f(0) ≠ 0`. -/
theorem fourierMultiplier_schwartz_bound (k l : ℕ) :
    ∃ deriv_order : ℕ, ∀ (B N : ℝ), ∃ (s : Finset (ℕ × ℕ)) (C' : ℝ), 0 < C' ∧
    ∀ (σ : ℝ → ℝ) (hσ : σ.HasTemperateGrowth),
      (∀ (m : ℕ), m ≤ deriv_order →
        ∀ p : ℝ, ‖iteratedDeriv m σ p‖ ≤ B * (1 + |p|) ^ N) →
      ∀ f : SchwartzMap ℝ ℝ,
        SchwartzMap.seminorm ℝ k l (realFourierMultiplierCLM σ hσ f) ≤
        C' * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  -- (i) the fixed output map `g ↦ re (𝓕⁻ g)` is continuous
  let Tout : SchwartzMap ℝ ℂ →L[ℝ] SchwartzMap ℝ ℝ :=
    schwartzToReal.comp (FourierTransform.fourierInvCLM ℝ (SchwartzMap ℝ ℂ))
  have hcont₁ : Continuous ((SchwartzMap.seminorm ℝ k l).comp Tout.toLinearMap) :=
    ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm (k, l)).comp Tout.continuous
  obtain ⟨s₁, C₁, -, h₁⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℂ) _ hcont₁
  set K₀ := s₁.sup Prod.fst
  set n₀ := s₁.sup Prod.snd
  have hs₁ : s₁ ⊆ Finset.Iic (K₀, n₀) := fun m hm =>
    Finset.mem_Iic.mpr ⟨Finset.le_sup (f := Prod.fst) hm, Finset.le_sup (f := Prod.snd) hm⟩
  refine ⟨n₀, fun B N => ?_⟩
  set L := ⌈N⌉₊
  -- (iii) the fixed input map `f ↦ 𝓕 (ofReal ∘ f)` is continuous
  let Tin : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℂ :=
    (FourierTransform.fourierCLM ℝ (SchwartzMap ℝ ℂ)).comp schwartzToComplex
  have hcont₃ : Continuous
      (((Finset.Iic (L + K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ)).comp Tin.toLinearMap) :=
    (Seminorm.continuous_finsetSup fun i _ =>
      (schwartz_withSeminorms ℝ ℝ ℂ).continuous_seminorm i).comp Tin.continuous
  obtain ⟨s₂, C₃, -, h₃⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ ℝ ℝ) _ hcont₃
  set C₂ : ℝ := 2 ^ n₀ * max B 0 * 2 ^ (L + K₀)
  have hC₂ : 0 ≤ C₂ := by positivity
  refine ⟨s₂, C₁ * C₂ * C₃ + 1, by positivity, fun σ hσ hderiv f => ?_⟩
  -- the symbol bound in `iteratedFDeriv` form with an integer exponent
  have hσB : ∀ m ≤ n₀, ∀ x : ℝ, ‖iteratedFDeriv ℝ m σ x‖ ≤ max B 0 * (1 + ‖x‖) ^ L := by
    intro m hm x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs x]
    have hx : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
    calc ‖iteratedDeriv m σ x‖ ≤ B * (1 + |x|) ^ N := hderiv m hm x
      _ ≤ max B 0 * (1 + |x|) ^ N := by gcongr; exact le_max_left _ _
      _ ≤ max B 0 * (1 + |x|) ^ (L : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx (Nat.le_ceil N))
            (le_max_right _ _)
      _ = max B 0 * (1 + |x|) ^ L := by rw [Real.rpow_natCast]
  set g := SchwartzMap.smulLeftCLM ℂ σ (Tin f)
  have hfac : realFourierMultiplierCLM σ hσ f = Tout g := rfl
  -- (ii) σ-uniform Leibniz bound on the finitely many seminorms in `s₁`
  have h₂ : (Finset.Iic (K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤
      C₂ * (Finset.Iic (L + K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (Tin f) := by
    refine Seminorm.finset_sup_apply_le (by positivity) fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_Iic.mp hm
    have hmono : (Finset.Iic (L + m.1, m.2)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (Tin f) ≤
        (Finset.Iic (L + K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (Tin f) :=
      Seminorm.le_def.mp (Finset.sup_mono (Finset.Iic_subset_Iic.mpr
        (Prod.mk_le_mk.mpr ⟨by omega, hm2⟩))) _
    calc schwartzSeminormFamily ℝ ℝ ℂ m g
        ≤ 2 ^ m.2 * max B 0 * 2 ^ (L + m.1) *
          (Finset.Iic (L + m.1, m.2)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (Tin f) :=
          schwartz_seminorm_smulLeftCLM_le hσ
            (fun m' hm' x => hσB m' (hm'.trans hm2) x) m.1 (Tin f)
      _ ≤ C₂ * (Finset.Iic (L + K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ) (Tin f) := by
          refine mul_le_mul (?_ : _ ≤ C₂) hmono (apply_nonneg _ _) hC₂
          have h1 : (2 : ℝ) ^ m.2 ≤ 2 ^ n₀ := pow_le_pow_right₀ (by norm_num) hm2
          have h2 : (2 : ℝ) ^ (L + m.1) ≤ 2 ^ (L + K₀) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          have h3 : 0 ≤ max B 0 := le_max_right _ _
          calc (2 : ℝ) ^ m.2 * max B 0 * 2 ^ (L + m.1)
              ≤ 2 ^ n₀ * max B 0 * 2 ^ (L + K₀) := by gcongr
            _ = C₂ := rfl
  have hq₁ := h₁ g
  have hq₃ := h₃ f
  simp only [Seminorm.comp_apply, smul_apply, NNReal.smul_def, smul_eq_mul,
    ContinuousLinearMap.coe_coe] at hq₁ hq₃
  have hsub : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤
      (Finset.Iic (K₀, n₀)).sup (schwartzSeminormFamily ℝ ℝ ℂ) g :=
    Seminorm.le_def.mp (Finset.sup_mono hs₁) g
  have hpos : 0 ≤ s₂.sup (schwartzSeminormFamily ℝ ℝ ℝ) f := apply_nonneg _ _
  rw [hfac]
  calc SchwartzMap.seminorm ℝ k l (Tout g)
      ≤ C₁ * s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) g := hq₁
    _ ≤ C₁ * (C₂ * (C₃ * s₂.sup (schwartzSeminormFamily ℝ ℝ ℝ) f)) := by
        gcongr
        exact hsub.trans (h₂.trans (by gcongr))
    _ = (C₁ * C₂ * C₃) * s₂.sup (schwartzSeminormFamily ℝ ℝ ℝ) f := by ring
    _ ≤ (C₁ * C₂ * C₃ + 1) * s₂.sup (schwartzSeminormFamily ℝ ℝ ℝ) f := by
        gcongr; linarith

end MultiplierSchwartzBound

/-! ## Uniform resolvent bound from the multiplier bound

The resolvent family `σ_ω(p) = (p² + ω²)^{-1/2}` for `ω ≥ mass > 0` has
uniform polynomial derivative bounds. The scaling identity
`σ_ω(p) = ω⁻¹ · σ₁(ω⁻¹ p)` reduces all derivative estimates to the fixed symbol
`σ₁`, and `σ₁` already has temperate growth by
`resolventSymbol_hasTemperateGrowth`. Applying
`fourierMultiplier_schwartz_bound` with the number of symbol derivatives it requires then
yields the uniform seminorm bound. -/

/-- Scaling identity for the resolvent symbol. -/
private theorem resolventSymbol_scaling' {ω : ℝ} (hω : 0 < ω) :
    resolventSymbol ω = fun p => ω⁻¹ * resolventSymbol 1 (ω⁻¹ * p) := by
  funext p
  unfold resolventSymbol
  have hfact : p ^ 2 + ω ^ 2 = ω ^ 2 * ((ω⁻¹ * p) ^ 2 + 1 ^ 2) := by
    have hω0 : ω ≠ 0 := hω.ne'
    field_simp [hω0]
  rw [hfact, Real.mul_rpow (le_of_lt (sq_pos_of_pos hω)) (by positivity)]
  congr 1
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg (sq_nonneg ω), ← Real.sqrt_eq_rpow, Real.sqrt_sq hω.le]

/-- Scaling of iterated derivatives of the resolvent symbol. -/
private theorem iteratedDeriv_resolventSymbol_scaling {ω : ℝ} (hω : 0 < ω) (m : ℕ) :
    iteratedDeriv m (resolventSymbol ω) =
      fun p => ω⁻¹ * (ω⁻¹) ^ m * iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p) := by
  have hcontTop := (resolventSymbol_hasTemperateGrowth 1 zero_lt_one).1
  have hcont : ContDiff ℝ m (resolventSymbol 1) := hcontTop.of_le
    (show (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  funext p
  rw [resolventSymbol_scaling' hω]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_mul hcont ω⁻¹]
  ring

theorem resolventSymbol_uniform_deriv_bound (mass : ℝ) (hmass : 0 < mass) (deriv_order : ℕ) :
    ∃ (B : ℝ) (N : ℕ), 0 < B ∧ ∀ (ω : ℝ), mass ≤ ω →
      ∀ (m : ℕ), m ≤ deriv_order →
        ∀ p : ℝ, ‖iteratedDeriv m (resolventSymbol ω) p‖ ≤ B * (1 + |p|) ^ (N : ℝ) := by
  have hσ1 := resolventSymbol_hasTemperateGrowth 1 zero_lt_one
  obtain ⟨k, C, hC, hσ1_bound⟩ := hσ1.norm_iteratedFDeriv_le_uniform deriv_order
  let A : ℝ := max 1 (1 / mass)
  have hA : 1 ≤ A := le_max_left _ _
  have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAω : ∀ ω : ℝ, mass ≤ ω → 1 / ω ≤ A := by
    intro ω hω
    exact le_trans (div_le_div_of_nonneg_left one_pos.le hmass hω) (le_max_right _ _)
  refine ⟨(C + 1) * A ^ (deriv_order + 1 + k), k, ?_, ?_⟩
  · have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
    positivity
  · intro ω hω m hm p
    have hω' : 0 < ω := lt_of_lt_of_le hmass hω
    have hσ1p : ‖iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p)‖ ≤
        C * (1 + |ω⁻¹ * p|) ^ k := by
      simpa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        hσ1_bound m hm (ω⁻¹ * p)
    have hωinv_le : ω⁻¹ ≤ A := by
      simpa [one_div] using hAω ω hω
    have hp_scale : 1 + |ω⁻¹ * p| ≤ A * (1 + |p|) := by
      calc
        1 + |ω⁻¹ * p| = 1 + ω⁻¹ * |p| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hω')]
        _ ≤ A + A * |p| := by
          gcongr
        _ = A * (1 + |p|) := by ring
    have hp_pow : (1 + |ω⁻¹ * p|) ^ k ≤ (A * (1 + |p|)) ^ k := by
      gcongr
    have hωpow : (ω⁻¹) ^ (m + 1) ≤ A ^ (deriv_order + 1) := by
      calc
        (ω⁻¹) ^ (m + 1) ≤ A ^ (m + 1) := by
          gcongr
        _ ≤ A ^ (deriv_order + 1) := by
          exact pow_le_pow_right₀ hA (Nat.succ_le_succ hm)
    have hAkpow : A ^ k ≤ A ^ (deriv_order + 1 + k) := by
      exact pow_le_pow_right₀ hA (Nat.le_add_left k (deriv_order + 1))
    have hAk : A ^ k * (1 + |p|) ^ (k : ℝ) ≤ A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
      exact mul_le_mul_of_nonneg_right hAkpow (by positivity)
    calc
      ‖iteratedDeriv m (resolventSymbol ω) p‖
          = (ω⁻¹) ^ (m + 1) * ‖iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p)‖ := by
              rw [iteratedDeriv_resolventSymbol_scaling hω' m]
              rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              have habsω : |ω| = ω := abs_of_pos hω'
              simp [habsω, abs_of_pos (inv_pos.mpr hω'), pow_succ, mul_assoc]
              ring
      _ ≤ (ω⁻¹) ^ (m + 1) * (C * (1 + |ω⁻¹ * p|) ^ k) := by
            gcongr
      _ ≤ A ^ (deriv_order + 1) * (C * (A * (1 + |p|)) ^ k) := by
            gcongr
      _ = C * A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
            rw [mul_pow]
            rw [show (1 + |p|) ^ k = (1 + |p|) ^ (k : ℝ) by rw [Real.rpow_natCast]]
            ring
      _ ≤ (C + 1) * A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
            gcongr
            linarith

theorem resolventSchwartz_uniformBound
    (mass : ℝ) (hmass : 0 < mass) (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ k l
        (resolventMultiplierCLM (lt_of_lt_of_le hmass (show mass ≤ ω from hω)) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  -- Step 1: the number of symbol derivatives needed for the `(k, l)` seminorm
  obtain ⟨D, hD⟩ := fourierMultiplier_schwartz_bound k l
  -- Step 2: uniform bounds on those derivatives for the resolvent family
  obtain ⟨B, N, -, h_deriv⟩ := resolventSymbol_uniform_deriv_bound mass hmass D
  -- Step 3: the multiplier bound with these parameters
  obtain ⟨s, C', hC', h_mult⟩ := hD B N
  -- Step 4: package
  refine ⟨s, C', hC', fun ω hω f => ?_⟩
  -- resolventMultiplierCLM hω' = realFourierMultiplierCLM (resolventSymbol ω) hσ
  have hω' := lt_of_lt_of_le hmass hω
  show SchwartzMap.seminorm ℝ k l (resolventMultiplierCLM hω' f) ≤ _
  rw [show resolventMultiplierCLM hω' =
    realFourierMultiplierCLM (resolventSymbol ω)
      (resolventSymbol_hasTemperateGrowth ω hω') from rfl]
  exact h_mult (resolventSymbol ω) (resolventSymbol_hasTemperateGrowth ω hω')
    (h_deriv ω hω) f

end GaussianField
