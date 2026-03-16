/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function Invariance under Torus Symmetries

Proves that the Green's function `G(f,g) = Σ c_m(f)·c_m(g)/(μ_m + mass²)`
on the torus tensor product is invariant under translation, reflection,
and coordinate swap.

## Main results

- `greenFunctionBilinear_reflection_pure` — G invariant under reflection on pure tensors
- `greenFunctionBilinear_swap_pure` — G invariant under swap on pure tensors
- `greenFunctionBilinear_translation_pure` — G invariant under translation on pure tensors
- `greenFunctionBilinear_invariant_of_pure` — extension from pure tensors to all elements
- `greenFunctionBilinear_timeReflection_invariant` — full reflection invariance (theorem)
- `greenFunctionBilinear_swap_invariant` — full swap invariance (theorem)
- `greenFunctionBilinear_translation_invariant` — full translation invariance (theorem)

## Mathematical background

On the torus `S¹_L ⊗ S¹_L`, the Green's function is
  `G(f,g) = Σ_{(n₁,n₂)} c_{n₁}(f₁)c_{n₂}(f₂) · c_{n₁}(g₁)c_{n₂}(g₂) / (μ₁(n₁) + μ₂(n₂) + m²)`
for pure tensors `f = f₁⊗f₂`, `g = g₁⊗g₂`.

**Reflection** `Θ⊗id`: Each factor `c_n(Θf)·c_n(Θg)` equals `(±1)²·c_n(f)·c_n(g)`,
so the sum is invariant term-by-term.

**Swap**: Relabel `(n₁,n₂) ↦ (n₂,n₁)` and use commutativity of addition.

**Translation**: Group the sum by degenerate frequency pairs (2k-1, 2k) in each
factor. The paired product `c_{2k-1}(Tf)·c_{2k-1}(Tg) + c_{2k}(Tf)·c_{2k}(Tg)`
is invariant (from `paired_coeff_product_circleTranslation`), and paired modes
share eigenvalues.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.4
-/

import SmoothCircle.FourierTranslation
import Nuclear.TensorProductFunctorAxioms

noncomputable section

namespace GaussianField

open NuclearTensorProduct SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Helper lemmas for pure tensor invariance -/

/-- DyninMityaginSpace coefficient equals Fourier coefficient for circle functions. -/
private theorem coeff_eq_fourierCoeffReal (m : ℕ) (f : SmoothMap_Circle L ℝ) :
    DyninMityaginSpace.coeff m f = fourierCoeffReal (L := L) m f := by
  show ((RapidDecaySeq.coeffCLM m).comp
    (smoothCircleRapidDecayEquiv (L := L)).toContinuousLinearMap) f = _
  simp [RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM,
    smoothCircleRapidDecayEquiv, toRapidDecayLM, toRapidDecay]

/-- Reflection preserves the product of Fourier coefficients at every index. -/
private theorem fourierCoeffReal_reflection_product (m : ℕ)
    (f g : SmoothMap_Circle L ℝ) :
    fourierCoeffReal (L := L) m (circleReflection L f) *
    fourierCoeffReal (L := L) m (circleReflection L g) =
    fourierCoeffReal (L := L) m f * fourierCoeffReal (L := L) m g := by
  cases m with
  | zero =>
    rw [fourierCoeffReal_circleReflection_zero, fourierCoeffReal_circleReflection_zero]
  | succ n =>
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n even → m = 2(j+1)-1 (cos mode, invariant)
      have : n + 1 = 2 * (j + 1) - 1 := by omega
      rw [this,
        fourierCoeffReal_circleReflection_cos (L := L) (j + 1) (by omega) f,
        fourierCoeffReal_circleReflection_cos (L := L) (j + 1) (by omega) g]
    · -- n odd → m = 2(j+1) (sin mode, negated, but (-a)(-b) = ab)
      have : n + 1 = 2 * (j + 1) := by omega
      rw [this,
        fourierCoeffReal_circleReflection_sin (L := L) (j + 1) (by omega) f,
        fourierCoeffReal_circleReflection_sin (L := L) (j + 1) (by omega) g]
      ring

/-! ## Pure tensor invariance -/

/-- **Green's function is invariant under time reflection on pure tensors.**

  `G(Θf₁⊗f₂, Θg₁⊗g₂) = G(f₁⊗f₂, g₁⊗g₂)`

Each term at index m has `c_n(Θf)·c_n(Θg) = (±1)²·c_n(f)·c_n(g)`,
so the sum is invariant term-by-term. -/
theorem greenFunctionBilinear_reflection_pure
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure (circleReflection L f₁) f₂)
      (NuclearTensorProduct.pure (circleReflection L g₁) g₂) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) := by
  -- Unfold to tsum, then show summands agree
  show ∑' m, DyninMityaginSpace.coeff m (pure (circleReflection L f₁) f₂) *
      DyninMityaginSpace.coeff m (pure (circleReflection L g₁) g₂) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2) =
    ∑' m, DyninMityaginSpace.coeff m (pure f₁ f₂) *
      DyninMityaginSpace.coeff m (pure g₁ g₂) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2)
  congr 1; ext m
  -- NTP coeff is .val, so rewrite to pure_val form
  show (pure (circleReflection L f₁) f₂).val m *
      (pure (circleReflection L g₁) g₂).val m /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2) =
    (pure f₁ f₂).val m * (pure g₁ g₂).val m /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2)
  simp only [pure_val]
  have h := fourierCoeffReal_reflection_product L (Nat.unpair m).1 f₁ g₁
  rw [← coeff_eq_fourierCoeffReal L _ (circleReflection L f₁),
      ← coeff_eq_fourierCoeffReal L _ (circleReflection L g₁),
      ← coeff_eq_fourierCoeffReal L _ f₁,
      ← coeff_eq_fourierCoeffReal L _ g₁] at h
  congr 1
  linear_combination
    DyninMityaginSpace.coeff (Nat.unpair m).2 f₂ *
    DyninMityaginSpace.coeff (Nat.unpair m).2 g₂ * h

/-- **Green's function is invariant under coordinate swap on pure tensors.**

  `G(f₂⊗f₁, g₂⊗g₁) = G(f₁⊗f₂, g₁⊗g₂)`

Proof: The spectral sum over `m = pair(n₁,n₂)` is reindexed
via `(n₁,n₂) ↦ (n₂,n₁)`, i.e., `m ↦ pair(unpair(m).2, unpair(m).1)`.
The numerator transforms as `c_{n₁}(f₂)·c_{n₂}(f₁) ↦ c_{n₂}(f₁)·c_{n₁}(f₂)`
(commutative multiplication). The denominator transforms as
`μ(n₁) + μ(n₂) + m² ↦ μ(n₂) + μ(n₁) + m²` (commutative addition).
So the reindexed sum equals the original. -/
theorem greenFunctionBilinear_swap_pure
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₂ f₁)
      (NuclearTensorProduct.pure g₂ g₁) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) := by
  -- The swap equivalence on ℕ via Cantor pairing: m ↦ pair(unpair(m).2, unpair(m).1)
  set σ : ℕ ≃ ℕ := Nat.pairEquiv.symm.trans
    ((Equiv.prodComm ℕ ℕ).trans Nat.pairEquiv) with hσ_def
  -- Abbreviation for the RHS summand
  set g := fun m =>
    DyninMityaginSpace.coeff m (pure f₁ f₂) *
      DyninMityaginSpace.coeff m (pure g₁ g₂) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2)
  -- Both sides are tsums (greenTerm is private, so unfold via show).
  show ∑' m, DyninMityaginSpace.coeff m (pure f₂ f₁) *
        DyninMityaginSpace.coeff m (pure g₂ g₁) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) =
      ∑' m, g m
  -- Step 1: Show LHS summand at m equals RHS summand at σ m, pointwise
  -- Key lemma: σ m simplifies to Nat.pair (Nat.unpair m).2 (Nat.unpair m).1
  have hσ_apply : ∀ m, σ m = Nat.pair (Nat.unpair m).2 (Nat.unpair m).1 := by
    intro m
    simp [hσ_def, Nat.pairEquiv, Equiv.prodComm_apply, Function.uncurry, Prod.swap]
  -- coeff m (pure e₁ e₂) = (pure e₁ e₂).val m (definitionally)
  -- pure_val: (pure e₁ e₂).val m = coeff (unpair m).1 e₁ * coeff (unpair m).2 e₂
  have h_eq : ∀ m, DyninMityaginSpace.coeff m (pure f₂ f₁) *
      DyninMityaginSpace.coeff m (pure g₂ g₁) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2) = g (σ m) := by
    intro m
    -- Unfold g, σ, and the NTP eigenvalue
    simp only [g, hσ_apply]
    -- coeff for NTP pure tensors decomposes as product of component coefficients
    have coeff_pure := fun (a b : SmoothMap_Circle L ℝ) (n : ℕ) =>
      show DyninMityaginSpace.coeff n (pure a b) =
        DyninMityaginSpace.coeff (Nat.unpair n).1 a *
        DyninMityaginSpace.coeff (Nat.unpair n).2 b from pure_val a b n
    -- NTP eigenvalue decomposes as sum of component eigenvalues
    have ev_ntp := fun (n : ℕ) =>
      show HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) n =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1 +
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair n).2 from rfl
    simp only [coeff_pure, ev_ntp, Nat.unpair_pair]
    ring
  -- Step 2: Rewrite LHS as ∑' m, g (σ m), then apply Equiv.tsum_eq
  simp_rw [h_eq]
  exact Equiv.tsum_eq σ g

/-! ### Eigenvalue degeneracy and mode-pair involution -/

/-- Fourier frequency degeneracy: `fourierFreq (2k-1) = fourierFreq (2k) = k`. -/
private theorem fourierFreq_cos_eq_sin (k : ℕ) (hk : 0 < k) :
    fourierFreq (2 * k - 1) = fourierFreq (2 * k) := by
  cases k with
  | zero => omega
  | succ k =>
    -- 2*(k+1)-1 = 2k+1, 2*(k+1) = 2k+2
    show fourierFreq (2 * k + 1) = fourierFreq (2 * k + 2)
    simp [fourierFreq]
    -- goal: k = (2 * k + 1) / 2  (omega can't handle division)
    have := Nat.div_add_mod (2 * k + 1) 2
    omega

/-- Eigenvalue degeneracy for the circle: paired cos/sin modes share eigenvalues. -/
private theorem circle_eigenvalue_cos_eq_sin (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (2 * k - 1) =
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (2 * k) := by
  have h := fourierFreq_cos_eq_sin k hk
  show (2 * Real.pi * ↑(fourierFreq (2 * k - 1)) / L) ^ 2 =
    (2 * Real.pi * ↑(fourierFreq (2 * k)) / L) ^ 2
  rw [h]

/-- The mode-partner involution on ℕ: swaps `2k-1 ↔ 2k` and fixes `0`.
For n ≥ 1: odd n maps to n+1, even n maps to n-1. -/
private def modePartner (n : ℕ) : ℕ :=
  if n = 0 then 0 else if n % 2 = 1 then n + 1 else n - 1

private theorem modePartner_involutive : Function.Involutive modePartner := by
  intro n
  simp only [modePartner]
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n % 2 = 1
    · -- n odd → partner = n+1 (even, nonzero)
      have : n + 1 ≠ 0 := by omega
      have : (n + 1) % 2 = 0 := by omega
      simp [*]
    · -- n even, n ≠ 0 → partner = n-1 (odd, nonzero)
      have hn1 : n - 1 ≠ 0 := by omega
      have hn2 : (n - 1) % 2 = 1 := by omega
      simp [h0, h1, hn1, hn2]
      omega

/-- The mode-partner as an equivalence on ℕ. -/
private def modePartnerEquiv : ℕ ≃ ℕ :=
  modePartner_involutive.toPerm modePartner

/-- modePartner maps 2k-1 ↦ 2k for k ≥ 1. -/
private theorem modePartner_cos (k : ℕ) (hk : 0 < k) :
    modePartner (2 * k - 1) = 2 * k := by
  simp only [modePartner]; split_ifs <;> omega

/-- modePartner maps 2k ↦ 2k-1 for k ≥ 1. -/
private theorem modePartner_sin (k : ℕ) (hk : 0 < k) :
    modePartner (2 * k) = 2 * k - 1 := by
  simp only [modePartner]; split_ifs <;> omega

/-- If summable `f` and `g` agree on involution-paired sums, their tsums agree.
This uses the "2x = 2y" argument via reindexing by the involution. -/
private theorem tsum_eq_of_paired_involution {σ : ℕ ≃ ℕ} {f g : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g)
    (h_pair : ∀ n, f n + f (σ n) = g n + g (σ n)) :
    ∑' n, f n = ∑' n, g n := by
  have hfσ : Summable (f ∘ ⇑σ) := (σ.summable_iff).mpr hf
  have hgσ : Summable (g ∘ ⇑σ) := (σ.summable_iff).mpr hg
  have h2f : ∑' n, (f n + f (σ n)) = 2 * ∑' n, f n := by
    change ∑' n, (f n + (f ∘ ⇑σ) n) = _
    rw [hf.tsum_add hfσ]
    change ∑' b, f b + ∑' b, f (σ b) = _
    rw [σ.tsum_eq f, two_mul]
  have h2g : ∑' n, (g n + g (σ n)) = 2 * ∑' n, g n := by
    change ∑' n, (g n + (g ∘ ⇑σ) n) = _
    rw [hg.tsum_add hgσ]
    change ∑' b, g b + ∑' b, g (σ b) = _
    rw [σ.tsum_eq g, two_mul]
  have h_eq : ∑' n, (f n + f (σ n)) = ∑' n, (g n + g (σ n)) :=
    tsum_congr h_pair
  linarith

/-- The paired product of Fourier coefficients is invariant under translation
for cos/sin mode pairs. -/
private theorem coeff_product_paired_translation (v : ℝ)
    (f g : SmoothMap_Circle L ℝ) (n : ℕ) :
    fourierCoeffReal (L := L) n (circleTranslation L v f) *
      fourierCoeffReal (L := L) n (circleTranslation L v g) +
    fourierCoeffReal (L := L) (modePartner n) (circleTranslation L v f) *
      fourierCoeffReal (L := L) (modePartner n) (circleTranslation L v g) =
    fourierCoeffReal (L := L) n f * fourierCoeffReal (L := L) n g +
    fourierCoeffReal (L := L) (modePartner n) f *
      fourierCoeffReal (L := L) (modePartner n) g := by
  match n with
  | 0 =>
    have : modePartner 0 = 0 := by simp [modePartner]
    rw [this, fourierCoeffReal_circleTranslation_zero, fourierCoeffReal_circleTranslation_zero]
  | n + 1 =>
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n even → n+1 = 2(j+1)-1 (cos mode), partner = 2(j+1)
      have hn1 : n + 1 = 2 * (j + 1) - 1 := by omega
      have hpartner : modePartner (n + 1) = 2 * (j + 1) := by
        rw [hn1]; exact modePartner_cos (j + 1) (by omega)
      rw [hpartner, hn1]
      exact paired_coeff_product_circleTranslation L (j + 1) (by omega) v f g
    · -- n odd → n+1 = 2(j+1) (sin mode), partner = 2(j+1)-1
      have hn1 : n + 1 = 2 * (j + 1) := by omega
      have hpartner : modePartner (n + 1) = 2 * (j + 1) - 1 := by
        rw [hn1]; exact modePartner_sin (j + 1) (by omega)
      rw [hpartner, hn1]
      have hinv := paired_coeff_product_circleTranslation L (j + 1) (by omega) v f g
      linarith

/-! ### Translation invariance on factor 1 only -/

/-- Green's function is invariant under translation on the first tensor factor. -/
private theorem greenFunctionBilinear_translation_factor1
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure (circleTranslation L v f₁) f₂)
      (NuclearTensorProduct.pure (circleTranslation L v g₁) g₂) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) := by
  -- Unfold to tsum
  show ∑' m, DyninMityaginSpace.coeff m (pure (circleTranslation L v f₁) f₂) *
      DyninMityaginSpace.coeff m (pure (circleTranslation L v g₁) g₂) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2) =
    ∑' m, DyninMityaginSpace.coeff m (pure f₁ f₂) *
      DyninMityaginSpace.coeff m (pure g₁ g₂) /
      (HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
        mass ^ 2)
  -- Define the involution on NTP index: swap mode partner in first component
  set σ : ℕ ≃ ℕ := (Nat.pairEquiv.symm.trans
    ((Equiv.prodCongrLeft fun _ => modePartnerEquiv).trans Nat.pairEquiv))
  -- Use paired involution: paired sums agree
  apply tsum_eq_of_paired_involution (σ := σ)
  · exact greenFunctionBilinear_summable mass hmass
      (pure (circleTranslation L v f₁) f₂) (pure (circleTranslation L v g₁) g₂)
  · exact greenFunctionBilinear_summable mass hmass (pure f₁ f₂) (pure g₁ g₂)
  · intro m
    -- σ m = pair(modePartner n₁, n₂) where (n₁, n₂) = unpair m
    have hσ : σ m = Nat.pair (modePartner (Nat.unpair m).1) (Nat.unpair m).2 := by
      simp [σ, Nat.pairEquiv, modePartnerEquiv, Function.Involutive.toPerm,
        Equiv.prodCongrLeft, Function.uncurry]
    -- Convert coeff to .val, use pure_val, unfold NTP eigenvalue
    show (pure (circleTranslation L v f₁) f₂).val m *
        (pure (circleTranslation L v g₁) g₂).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) +
      (pure (circleTranslation L v f₁) f₂).val (σ m) *
        (pure (circleTranslation L v g₁) g₂).val (σ m) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) (σ m) +
          mass ^ 2) =
      (pure f₁ f₂).val m * (pure g₁ g₂).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) +
      (pure f₁ f₂).val (σ m) * (pure g₁ g₂).val (σ m) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) (σ m) +
          mass ^ 2)
    -- NTP eigenvalue decomposes as sum of component eigenvalues
    have ev_ntp := fun (n : ℕ) =>
      show HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) n =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1 +
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair n).2 from rfl
    simp only [pure_val, hσ, Nat.unpair_pair, ev_ntp]
    -- Eigenvalue degeneracy: eigenvalue(modePartner n₁) = eigenvalue(n₁)
    have h_ev : HasLaplacianEigenvalues.eigenvalue
        (E := SmoothMap_Circle L ℝ) (modePartner (Nat.unpair m).1) =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair m).1 := by
      set n₁ := (Nat.unpair m).1
      by_cases h0 : n₁ = 0
      · simp [h0, modePartner]
      · by_cases h1 : n₁ % 2 = 1
        · -- n₁ odd = 2k-1, partner = 2k
          obtain ⟨k, hk_pos, hk_eq⟩ : ∃ k, 0 < k ∧ n₁ = 2 * k - 1 := by
            use (n₁ + 1) / 2; constructor <;> omega
          rw [hk_eq, modePartner_cos k hk_pos]
          exact (circle_eigenvalue_cos_eq_sin L k hk_pos).symm
        · -- n₁ even ≥ 2 = 2k, partner = 2k-1
          obtain ⟨k, hk_pos, hk_eq⟩ : ∃ k, 0 < k ∧ n₁ = 2 * k := by
            use n₁ / 2; constructor <;> omega
          rw [hk_eq, modePartner_sin k hk_pos]
          exact circle_eigenvalue_cos_eq_sin L k hk_pos
    rw [h_ev]
    -- Denominators now equal. Use coeff_eq_fourierCoeffReal and paired invariance.
    set D := HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair m).1 +
      HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (Nat.unpair m).2 +
      mass ^ 2
    set c₂f := DyninMityaginSpace.coeff (Nat.unpair m).2 f₂
    set c₂g := DyninMityaginSpace.coeff (Nat.unpair m).2 g₂
    -- Convert DMS coeff to fourierCoeffReal for the first factor
    have hcT1 := coeff_eq_fourierCoeffReal L (Nat.unpair m).1 (circleTranslation L v f₁)
    have hcT2 := coeff_eq_fourierCoeffReal L (Nat.unpair m).1 (circleTranslation L v g₁)
    have hcP1 := coeff_eq_fourierCoeffReal L (modePartner (Nat.unpair m).1) (circleTranslation L v f₁)
    have hcP2 := coeff_eq_fourierCoeffReal L (modePartner (Nat.unpair m).1) (circleTranslation L v g₁)
    have hc1 := coeff_eq_fourierCoeffReal L (Nat.unpair m).1 f₁
    have hc2 := coeff_eq_fourierCoeffReal L (Nat.unpair m).1 g₁
    have hcQ1 := coeff_eq_fourierCoeffReal L (modePartner (Nat.unpair m).1) f₁
    have hcQ2 := coeff_eq_fourierCoeffReal L (modePartner (Nat.unpair m).1) g₁
    rw [hcT1, hcT2, hcP1, hcP2, hc1, hc2, hcQ1, hcQ2]
    have h_paired := coeff_product_paired_translation L v f₁ g₁ (Nat.unpair m).1
    -- Clear division by D (which is positive)
    have hD_pos : 0 < D := by
      simp only [D]
      linarith [HasLaplacianEigenvalues.eigenvalue_nonneg
        (E := SmoothMap_Circle L ℝ) (Nat.unpair m).1,
        HasLaplacianEigenvalues.eigenvalue_nonneg
        (E := SmoothMap_Circle L ℝ) (Nat.unpair m).2,
        sq_pos_of_pos hmass]
    rw [← add_div, ← add_div, div_eq_div_iff hD_pos.ne' hD_pos.ne']
    linear_combination c₂f * c₂g * D * h_paired

/-- **Green's function is invariant under translation on pure tensors.**

  `G(T_{v₁}f₁⊗T_{v₂}f₂, T_{v₁}g₁⊗T_{v₂}g₂) = G(f₁⊗f₂, g₁⊗g₂)`

Combines factor-1 translation invariance with swap invariance to handle
both factors. -/
theorem greenFunctionBilinear_translation_pure
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure (circleTranslation L v.1 f₁)
                                 (circleTranslation L v.2 f₂))
      (NuclearTensorProduct.pure (circleTranslation L v.1 g₁)
                                 (circleTranslation L v.2 g₂)) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) := by
  -- Translate factor 2 using swap + factor1 + swap, then factor 1
  trans greenFunctionBilinear mass hmass
    (NuclearTensorProduct.pure (circleTranslation L v.2 f₂) (circleTranslation L v.1 f₁))
    (NuclearTensorProduct.pure (circleTranslation L v.2 g₂) (circleTranslation L v.1 g₁))
  · exact (greenFunctionBilinear_swap_pure L mass hmass _ _ _ _).symm
  trans greenFunctionBilinear mass hmass
    (NuclearTensorProduct.pure f₂ (circleTranslation L v.1 f₁))
    (NuclearTensorProduct.pure g₂ (circleTranslation L v.1 g₁))
  · exact greenFunctionBilinear_translation_factor1 L mass hmass v.2 f₂ g₂ _ _
  trans greenFunctionBilinear mass hmass
    (NuclearTensorProduct.pure (circleTranslation L v.1 f₁) f₂)
    (NuclearTensorProduct.pure (circleTranslation L v.1 g₁) g₂)
  · exact greenFunctionBilinear_swap_pure L mass hmass _ _ _ _
  exact greenFunctionBilinear_translation_factor1 L mass hmass v.1 f₁ g₁ f₂ g₂

/-! ## Extension from pure tensors to all elements -/

/-- Continuity of `f ↦ G(f, h)` for fixed `h`, derived from diagonal continuity
via polarization: `G(f,h) = (G(f+h,f+h) - G(f,f) - G(h,h))/2`. -/
private theorem greenFunctionBilinear_continuous_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) :
    Continuous (fun f => greenFunctionBilinear mass hmass f h) := by
  have hcdiag := greenFunctionBilinear_continuous_diag mass hmass (E := E)
  have hpol : ∀ f, greenFunctionBilinear mass hmass f h =
      (greenFunctionBilinear mass hmass (f + h) (f + h) -
       greenFunctionBilinear mass hmass f f -
       greenFunctionBilinear mass hmass h h) / 2 := by
    intro f
    have : greenFunctionBilinear mass hmass (f + h) (f + h) =
        greenFunctionBilinear mass hmass f f +
        2 * greenFunctionBilinear mass hmass f h +
        greenFunctionBilinear mass hmass h h := by
      rw [greenFunctionBilinear_add_left, greenFunctionBilinear_add_right,
          greenFunctionBilinear_add_right, greenFunctionBilinear_symm mass hmass h f]
      ring
    linarith
  exact (((hcdiag.comp (continuous_id.add continuous_const)).sub hcdiag).sub
    continuous_const).div_const 2 |>.congr (fun f => (hpol f).symm)

/-- The Green function as a CLM in the first argument, for fixed second argument. -/
private noncomputable def greenCLM_left
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h : E) : E →L[ℝ] ℝ :=
  ⟨{ toFun := fun f => greenFunctionBilinear mass hmass f h
     map_add' := fun f₁ f₂ => greenFunctionBilinear_add_left mass hmass f₁ f₂ h
     map_smul' := fun c f => by
       rw [greenFunctionBilinear_smul_left, RingHom.id_apply, smul_eq_mul] },
   greenFunctionBilinear_continuous_left mass hmass h⟩

@[simp] private theorem greenCLM_left_apply
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (h f : E) :
    greenCLM_left mass hmass h f = greenFunctionBilinear mass hmass f h := rfl

/-- Each NTP basis element is a pure tensor of component basis elements,
assuming biorthogonality `coeff n (basis m) = δ_{n,m}` in each factor. -/
private theorem ntp_basis_eq_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (hbasis₁ : ∀ n m, DyninMityaginSpace.coeff (E := E₁) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (hbasis₂ : ∀ n m, DyninMityaginSpace.coeff (E := E₂) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (m : ℕ) :
    DyninMityaginSpace.basis (E := NuclearTensorProduct E₁ E₂) m =
    pure (DyninMityaginSpace.basis (E := E₁) (Nat.unpair m).1)
         (DyninMityaginSpace.basis (E := E₂) (Nat.unpair m).2) := by
  ext k
  show (RapidDecaySeq.basisVec m).val k =
    (pure (DyninMityaginSpace.basis (E := E₁) (Nat.unpair m).1)
          (DyninMityaginSpace.basis (E := E₂) (Nat.unpair m).2)).val k
  rw [pure_val, hbasis₁, hbasis₂]
  simp only [RapidDecaySeq.basisVec]
  by_cases hk : k = m
  · subst hk; simp
  · simp only [hk, ite_false]
    by_cases h1 : (Nat.unpair k).1 = (Nat.unpair m).1
    · have h2 : (Nat.unpair k).2 ≠ (Nat.unpair m).2 := by
        intro h2
        exact hk (by rw [← Nat.pair_unpair k, h1, h2, Nat.pair_unpair])
      simp [h2]
    · simp [h1]

/-- **Green's function invariance extends from pure tensors to all elements.**

Uses a two-step expansion argument: first fix a pure tensor in the second
argument and use the DM expansion to show invariance for all first arguments;
then fix an arbitrary first argument and expand in the second. -/
theorem greenFunctionBilinear_invariant_of_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂]
    (hbasis₁ : ∀ n m, DyninMityaginSpace.coeff (E := E₁) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (hbasis₂ : ∀ n m, DyninMityaginSpace.coeff (E := E₂) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0)
    (mass : ℝ) (hmass : 0 < mass)
    (S : NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₁ E₂)
    (hpure : ∀ (e₁ : E₁) (e₂ : E₂) (e₁' : E₁) (e₂' : E₂),
      greenFunctionBilinear mass hmass (S (pure e₁ e₂)) (S (pure e₁' e₂')) =
      greenFunctionBilinear mass hmass (pure e₁ e₂) (pure e₁' e₂'))
    (f g : NuclearTensorProduct E₁ E₂) :
    greenFunctionBilinear mass hmass (S f) (S g) =
    greenFunctionBilinear mass hmass f g := by
  -- Phase A: G(Sf, Sh) = G(f, h) for all f and all pure h
  suffices phase_A : ∀ (e₁' : E₁) (e₂' : E₂) (f' : NuclearTensorProduct E₁ E₂),
      greenFunctionBilinear mass hmass (S f') (S (pure e₁' e₂')) =
      greenFunctionBilinear mass hmass f' (pure e₁' e₂') by
    -- Phase B: fix f, expand in g using DM expansion
    -- CLM: g ↦ G(Sg, Sf) - G(g, f) = (greenCLM_left(Sf) ∘ S - greenCLM_left(f))(g)
    set ψ_B : NuclearTensorProduct E₁ E₂ →L[ℝ] ℝ :=
      (greenCLM_left mass hmass (S f)).comp S -
       greenCLM_left mass hmass f
    have hψ_B : ∀ n, ψ_B (DyninMityaginSpace.basis n) = 0 := by
      intro n
      simp only [ψ_B, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        greenCLM_left_apply, sub_eq_zero]
      rw [ntp_basis_eq_pure hbasis₁ hbasis₂ n,
          greenFunctionBilinear_symm mass hmass (S _) (S f),
          greenFunctionBilinear_symm mass hmass (pure _ _) f]
      exact phase_A _ _ f
    have hexp := DyninMityaginSpace.expansion ψ_B g
    have hzero : ψ_B g = 0 := by
      rw [hexp]; convert tsum_zero with n; rw [hψ_B, mul_zero]
    simp only [ψ_B, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      greenCLM_left_apply, sub_eq_zero] at hzero
    rwa [greenFunctionBilinear_symm mass hmass (S g) (S f),
         greenFunctionBilinear_symm mass hmass g f] at hzero
  -- Prove Phase A: fix pure h, expand in f
  intro e₁' e₂' f'
  set ψ_A : NuclearTensorProduct E₁ E₂ →L[ℝ] ℝ :=
    (greenCLM_left mass hmass (S (pure e₁' e₂'))).comp S -
     greenCLM_left mass hmass (pure e₁' e₂')
  have hψ_A : ∀ n, ψ_A (DyninMityaginSpace.basis n) = 0 := by
    intro n
    simp only [ψ_A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      greenCLM_left_apply, sub_eq_zero]
    rw [ntp_basis_eq_pure hbasis₁ hbasis₂ n]
    exact hpure _ _ e₁' e₂'
  have hexp := DyninMityaginSpace.expansion ψ_A f'
  have hzero : ψ_A f' = 0 := by
    rw [hexp]; convert tsum_zero with n; rw [hψ_A, mul_zero]
  simp only [ψ_A, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    greenCLM_left_apply, sub_eq_zero] at hzero
  exact hzero

/-! ## Biorthogonality for SmoothMap_Circle -/

/-- The DyninMityaginSpace basis for `SmoothMap_Circle L ℝ` (constructed via
`ofRapidDecayEquiv`) satisfies biorthogonality: `coeff n (basis m) = δ_{nm}`. -/
theorem smoothCircle_coeff_basis (n m : ℕ) :
    DyninMityaginSpace.coeff (E := SmoothMap_Circle L ℝ) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0 := by
  show (RapidDecaySeq.coeffCLM n).comp
    (smoothCircleRapidDecayEquiv (L := L)).toContinuousLinearMap
    ((smoothCircleRapidDecayEquiv (L := L)).symm (RapidDecaySeq.basisVec m)) =
    if n = m then 1 else 0
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
    RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM, RapidDecaySeq.basisVec]

/-! ## Full invariance theorems

These combine the pure-tensor axioms with the extension principle
and the `mapCLM_pure` / `swapCLM_pure` specifications. -/

/-- **Green's function is invariant under time reflection.**

  `G(Θf, Θg) = G(f, g)` for all torus test functions f, g.

Combines `mapCLM_pure` (to reduce to pure tensors), `reflection_pure`
(invariance on pure tensors), and `invariant_of_pure` (extension). -/
theorem greenFunctionBilinear_timeReflection_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_mapCLM (circleReflection L)
        (ContinuousLinearMap.id ℝ _) f)
      (nuclearTensorProduct_mapCLM (circleReflection L)
        (ContinuousLinearMap.id ℝ _) g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure (smoothCircle_coeff_basis L)
    (smoothCircle_coeff_basis L) mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_mapCLM_pure, nuclearTensorProduct_mapCLM_pure]
  simp only [ContinuousLinearMap.id_apply]
  exact greenFunctionBilinear_reflection_pure L mass hmass e₁ e₁' e₂ e₂'

/-- **Green's function is invariant under coordinate swap.**

  `G(swap f, swap g) = G(f, g)` for all torus test functions f, g.

Note: `swapCLM : NTP E E → NTP E E` (both factors are the same type
for the square torus). -/
theorem greenFunctionBilinear_swap_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_swapCLM f)
      (nuclearTensorProduct_swapCLM g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure (smoothCircle_coeff_basis L)
    (smoothCircle_coeff_basis L) mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_swapCLM_pure, nuclearTensorProduct_swapCLM_pure]
  exact greenFunctionBilinear_swap_pure L mass hmass e₁ e₁' e₂ e₂'

/-- **Green's function is invariant under translation.**

  `G(T_v f, T_v g) = G(f, g)` for all v ∈ ℝ² and torus test functions f, g. -/
theorem greenFunctionBilinear_translation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_mapCLM (circleTranslation L v.1)
        (circleTranslation L v.2) f)
      (nuclearTensorProduct_mapCLM (circleTranslation L v.1)
        (circleTranslation L v.2) g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure (smoothCircle_coeff_basis L)
    (smoothCircle_coeff_basis L) mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_mapCLM_pure, nuclearTensorProduct_mapCLM_pure]
  exact greenFunctionBilinear_translation_pure L mass hmass v e₁ e₁' e₂ e₂'

end GaussianField

end
