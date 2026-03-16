/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Extension Theorem for Schwartz Spaces

Proves that every continuous multilinear functional on Schwartz spaces extends
uniquely to a continuous linear functional on the Schwartz space of the product domain.

## Main results

- `DyninMityaginSpace.clm_eq_of_basis_eq` — CLMs on DM spaces are determined by basis values
- `DyninMityaginSpace.exists_unique_clm_of_polyBounded` — existence and uniqueness of CLM
  from polynomially bounded basis values

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. I §3
- Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13
-/

import SchwartzNuclear.HermiteNuclear
import Mathlib.Topology.Algebra.InfiniteSum.Ring

noncomputable section

open GaussianField

namespace GaussianField

/-! ## Section 1: DyninMityaginSpace CLM Uniqueness -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

/-- Two CLMs agreeing on all basis vectors of a DyninMityaginSpace are equal. -/
theorem DyninMityaginSpace.clm_eq_of_basis_eq
    (φ₁ φ₂ : E →L[ℝ] ℝ)
    (h : ∀ m : ℕ, φ₁ (DyninMityaginSpace.basis m) = φ₂ (DyninMityaginSpace.basis m)) :
    φ₁ = φ₂ := by
  ext f
  rw [DyninMityaginSpace.expansion φ₁ f, DyninMityaginSpace.expansion φ₂ f]
  exact tsum_congr (fun m => by rw [h m])

/-! ## Section 2: CLM Construction from Basis Values -/

/-- A sequence has polynomial growth: bounded by `C · (1+m)^p`. -/
def PolyBounded (v : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ p : ℕ, ∀ m, |v m| ≤ C * (1 + (m : ℝ)) ^ p

/-- `Σ coeff_m(f) · v_m` converges when `v` has polynomial growth.
Uses `coeff_decay` at high enough index to dominate the growth of `v`. -/
theorem DyninMityaginSpace.summable_coeff_mul_polyBounded
    (v : ℕ → ℝ) (hv : PolyBounded v) (f : E) :
    Summable (fun m => DyninMityaginSpace.coeff m f * v m) := by
  obtain ⟨Cv, hCv, p, hv_bound⟩ := hv
  obtain ⟨Cc, hCc, s, hc_bound⟩ := DyninMityaginSpace.coeff_decay (E := E) (p + 2)
  apply Summable.of_norm
  have h_dom : ∀ m, ‖DyninMityaginSpace.coeff (E := E) m f * v m‖ ≤
      Cv * Cc * (s.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
    intro m
    have h1 : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    rw [Real.norm_eq_abs, abs_mul]
    have h_pow : (1 + (m : ℝ)) ^ p = (1 + (m : ℝ)) ^ (p + 2) * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
      rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h1.ne'), mul_one]
    calc |DyninMityaginSpace.coeff (E := E) m f| * |v m|
        ≤ |DyninMityaginSpace.coeff (E := E) m f| * (Cv * (1 + (m : ℝ)) ^ p) :=
          mul_le_mul_of_nonneg_left (hv_bound m) (abs_nonneg _)
      _ = Cv * (|DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ (p + 2)) *
            ((1 + (m : ℝ)) ^ 2)⁻¹ := by rw [h_pow]; ring
      _ ≤ Cv * (Cc * (s.sup DyninMityaginSpace.p) f) *
            ((1 + (m : ℝ)) ^ 2)⁻¹ := by
          apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (pow_nonneg h1.le 2))
          exact mul_le_mul_of_nonneg_left (hc_bound f m) hCv.le
      _ = Cv * Cc * (s.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by ring
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_dom
    -- Σ C/(1+m)^2: constant times shifted p-series with exponent 2 > 1
    (by exact (sorry : Summable fun (b : ℕ) => Cv * Cc * (s.sup DyninMityaginSpace.p) f *
      ((1 + (b : ℝ)) ^ 2)⁻¹))

/-- `f ↦ Σ coeff_m(f) · v_m` is a continuous linear functional when `v` has
polynomial growth. Linearity from `coeff`; continuity from the uniform bound
`|Σ c_m v_m| ≤ C · p_s(f)`. -/
def DyninMityaginSpace.clm_of_polyBounded (v : ℕ → ℝ) (hv : PolyBounded v) :
    E →L[ℝ] ℝ := by
  exact
  { toFun := fun f => ∑' m, DyninMityaginSpace.coeff (E := E) m f * v m
    map_add' := fun f g => by
      have hsf := summable_coeff_mul_polyBounded (E := E) v hv f
      have hsg := summable_coeff_mul_polyBounded (E := E) v hv g
      rw [show (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) +
        (∑' m, DyninMityaginSpace.coeff (E := E) m g * v m) =
        ∑' m, (DyninMityaginSpace.coeff (E := E) m f * v m +
          DyninMityaginSpace.coeff (E := E) m g * v m) from
        (hsf.tsum_add hsg).symm]
      exact tsum_congr (fun m => by
        simp [map_add, add_mul])
    map_smul' := fun r f => by
      simp only [RingHom.id_apply]
      rw [show r • (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) =
        r * (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) from rfl,
        ← tsum_mul_left]
      exact tsum_congr (fun m => by
        simp [map_smul, smul_eq_mul, mul_assoc])
    cont := by sorry }

/-- The CLM agrees with v on basis vectors (biorthogonal basis). -/
theorem DyninMityaginSpace.clm_of_polyBounded_basis
    [DyninMityaginSpace.HasBiorthogonalBasis E]
    (v : ℕ → ℝ) (hv : PolyBounded v) (m : ℕ) :
    DyninMityaginSpace.clm_of_polyBounded (E := E) v hv
      (DyninMityaginSpace.basis (E := E) m) = v m := by
  change ∑' n, DyninMityaginSpace.coeff (E := E) n
    (DyninMityaginSpace.basis (E := E) m) * v n = v m
  rw [tsum_eq_single m]
  · simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis]
  · intro n hn
    simp [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis, hn]

/-- **DyninMityaginSpace extension theorem**: Given polynomially bounded values
on basis vectors, there exists a unique CLM realizing those values. -/
theorem DyninMityaginSpace.exists_unique_clm_of_polyBounded
    [DyninMityaginSpace.HasBiorthogonalBasis E]
    (v : ℕ → ℝ) (hv : PolyBounded v) :
    ∃! (φ : E →L[ℝ] ℝ), ∀ m, φ (DyninMityaginSpace.basis m) = v m := by
  exact ⟨clm_of_polyBounded v hv, clm_of_polyBounded_basis v hv, fun φ' hφ' =>
    (clm_eq_of_basis_eq _ _ (fun m => by
      rw [hφ' m, clm_of_polyBounded_basis v hv m])).symm⟩

/-! ## Section 3: Schwartz Nuclear Extension

### Strategy for proving `schwartz_nuclear_extension`

The axiom in OSreconstruction states:
```
axiom schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (SchwartzMap.productTensor fs) = Phi fs
```

**Uniqueness** (from Section 1):
- A ℂ-linear `W` is determined by `w := W|_{S(prod,ℝ)}` via `W(f) = w(Re f) + i·w(Im f)`
- `w` is ℝ-linear, and by `clm_eq_of_basis_eq`, determined by values on Hermite basis
- Each Hermite basis element is a product tensor (factorization below)
- So `W` is uniquely determined by `Phi`

**Existence** (from Section 2):
- Restrict `Phi` to real Schwartz functions → ℝ-multilinear `Phi_ℝ : S(D,ℝ)^n → ℂ`
- Real/imaginary parts: `Re(Phi_ℝ)`, `Im(Phi_ℝ)` each ℝ-multilinear to ℝ
- Hermite basis functions of S(prod,ℝ) factor: `ψ_m = ψ_{β₁} ⊗ ··· ⊗ ψ_{βₙ}`
- Set `v_m := Re(Phi_ℝ(ψ_{β₁},...,ψ_{βₙ}))` — polynomially bounded by `basis_growth`
- Apply `clm_of_polyBounded` to get `w_re : S(prod,ℝ) →L[ℝ] ℝ`
- Similarly for `w_im`, then `w := w_re + i·w_im : S(prod,ℝ) →L[ℝ] ℂ`
- Complexify: `W(f) := w(Re f) + i·w(Im f)` — this is ℂ-linear and continuous
- Agreement on product tensors from coefficient factorization + multilinearity

### Key sorry targets

The following lemmas are needed to complete the proof: -/

/-- **Hermite basis factorization**: Each Hermite basis function of
`S(Fin n → D, ℝ)` factors as a product of individual-factor Hermite functions.

For `ψ_m ∈ S(ℝ^{n·dim(D)}, ℝ)` with flattened index `m`:
  `ψ_m(x₁,...,xₙ) = ψ_{β₁(m)}(x₁) · ... · ψ_{βₙ(m)}(xₙ)`

where `(β₁,...,βₙ)` comes from iterated Cantor unpairing of `m` into `n` groups.

This follows from:
- `hermiteFunctionNd_unpair`: multi-d Hermite functions factor via Cantor unpairing
- `schwartzRapidDecayEquiv` builds the basis from `hermiteFunctionNd`
- The coordinate equivalence `toEuclidean` preserves the product structure -/
theorem schwartz_basis_isProductTensor
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    ∃ (βs : Fin n → ℕ),
    ∀ (x : Fin n → D),
      haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
      haveI : Nontrivial (Fin n → D) := Pi.nontrivial
      @DyninMityaginSpace.basis (SchwartzMap (Fin n → D) ℝ) _ _ _ _ _
        (schwartz_dyninMityaginSpace (D := Fin n → D)) m
        (fun i => x i) =
      ∏ i : Fin n,
        @DyninMityaginSpace.basis (SchwartzMap D ℝ) _ _ _ _ _
          (schwartz_dyninMityaginSpace (D := D)) (βs i) (x i) := by
  sorry

/-- **Multilinear on basis is polynomially bounded**: For a continuous ℝ-multilinear
`Phi : S(D,ℝ)^n → ℝ`, the values `Phi(ψ_{β₁},...,ψ_{βₙ})` grow polynomially.

Follows from continuity of `Phi` (seminorm bound) and `basis_growth`. -/
theorem multilinear_on_basis_polyBounded
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ)
    (Phi : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℝ)
    (βs : ℕ → Fin n → ℕ) :
    PolyBounded (fun m => Phi (fun i =>
      @DyninMityaginSpace.basis (SchwartzMap D ℝ) _ _ _ _ _
        (schwartz_dyninMityaginSpace (D := D)) (βs m i))) := by
  sorry

/-- **Coefficient factorization**: Hermite coefficients of a product function
factorize as a product of individual-factor coefficients.

For `f(x₁,...,xₙ) = g₁(x₁) · ... · gₙ(xₙ)`:
  `coeff_m(f) = ∏ᵢ coeff_{βᵢ(m)}(gᵢ)`

This uses Fubini's theorem for the Hermite coefficient integral and the
factorization of multi-dimensional Hermite functions. -/
theorem schwartz_coeff_productTensor_factorize
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n) (gs : Fin n → SchwartzMap D ℝ) (m : ℕ)
    (βs : Fin n → ℕ)
    (h_factor : ∀ (x : Fin n → D),
      haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
      haveI : Nontrivial (Fin n → D) := Pi.nontrivial
      @DyninMityaginSpace.basis (SchwartzMap (Fin n → D) ℝ) _ _ _ _ _
        (schwartz_dyninMityaginSpace (D := Fin n → D)) m (fun i => x i) =
      ∏ i, @DyninMityaginSpace.basis (SchwartzMap D ℝ) _ _ _ _ _
        (schwartz_dyninMityaginSpace (D := D)) (βs i) (x i)) :
    haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩;
    haveI : Nontrivial (Fin n → D) := Pi.nontrivial;
    @DyninMityaginSpace.coeff (SchwartzMap (Fin n → D) ℝ) _ _ _ _ _
      (schwartz_dyninMityaginSpace (D := Fin n → D)) m
      ⟨fun x => ∏ i, gs i (x i), sorry, sorry⟩ =
    ∏ i, @DyninMityaginSpace.coeff (SchwartzMap D ℝ) _ _ _ _ _
      (schwartz_dyninMityaginSpace (D := D)) (βs i) (gs i) := by
  sorry

end GaussianField
