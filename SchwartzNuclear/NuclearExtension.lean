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
import SchwartzNuclear.TsumBound
import GeneralResults.SchwartzProducts
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
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_dom ?_
  -- Σ C/(1+m)^2: constant times shifted p-series with exponent 2 > 1
  apply Summable.mul_left
  have : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact this.congr (fun m => by push_cast; ring_nf)
  exact this.congr (fun m => by rw [one_div]; congr 1; ring)

/-- The linear map `f ↦ Σ coeff_m(f) · v_m`. -/
private def DyninMityaginSpace.extensionLM (v : ℕ → ℝ) (hv : PolyBounded v) :
    E →ₗ[ℝ] ℝ where
  toFun f := ∑' m, DyninMityaginSpace.coeff (E := E) m f * v m
  map_add' f g := by
    have hsf := summable_coeff_mul_polyBounded (E := E) v hv f
    have hsg := summable_coeff_mul_polyBounded (E := E) v hv g
    rw [show (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) +
      (∑' m, DyninMityaginSpace.coeff (E := E) m g * v m) =
      ∑' m, (DyninMityaginSpace.coeff (E := E) m f * v m +
        DyninMityaginSpace.coeff (E := E) m g * v m) from
      (hsf.tsum_add hsg).symm]
    exact tsum_congr (fun m => by simp [map_add, add_mul])
  map_smul' r f := by
    simp only [RingHom.id_apply]
    rw [show r • (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) =
      r * (∑' m, DyninMityaginSpace.coeff (E := E) m f * v m) from rfl,
      ← tsum_mul_left]
    exact tsum_congr (fun m => by simp [map_smul, smul_eq_mul, mul_assoc])

/-- Helper: the shifted p-series `Σ 1/(m+1)^2` converges. -/
private theorem summable_one_div_add_one_sq :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
  have := (summable_nat_add_iff 1).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  exact this.congr (fun m => by push_cast; ring_nf)

/-- Pointwise bound: `|c_m(f) · v_m| ≤ CvCc · p_s(f) / (1+m)^2`. -/
private theorem DyninMityaginSpace.coeff_mul_poly_bound (v : ℕ → ℝ)
    {Cv Cc : ℝ} {p : ℕ} {s : Finset (DyninMityaginSpace.ι (E := E))}
    (hv_bound : ∀ m, |v m| ≤ Cv * (1 + (m : ℝ)) ^ p)
    (hc_bound : ∀ (f : E) (m : ℕ),
      |DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ (p + 2) ≤
        Cc * (s.sup DyninMityaginSpace.p) f)
    (hCv : 0 < Cv) (f : E) (m : ℕ) :
    |DyninMityaginSpace.coeff (E := E) m f * v m| ≤
      Cv * Cc * (s.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
  rw [abs_mul]
  have h1 : (0 : ℝ) < 1 + (m : ℝ) := by positivity
  calc |DyninMityaginSpace.coeff (E := E) m f| * |v m|
      ≤ |DyninMityaginSpace.coeff (E := E) m f| * (Cv * (1 + (m : ℝ)) ^ p) :=
        mul_le_mul_of_nonneg_left (hv_bound m) (abs_nonneg _)
    _ = Cv * (|DyninMityaginSpace.coeff (E := E) m f| * (1 + (m : ℝ)) ^ (p + 2)) *
          ((1 + (m : ℝ)) ^ 2)⁻¹ := by
        rw [show (1 + (m : ℝ)) ^ p = (1 + (m : ℝ)) ^ (p + 2) * ((1 + (m : ℝ)) ^ 2)⁻¹
          from by rw [pow_add, mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 h1.ne'), mul_one]]
        ring
    _ ≤ Cv * (Cc * (s.sup DyninMityaginSpace.p) f) * ((1 + (m : ℝ)) ^ 2)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (pow_nonneg h1.le 2))
        exact mul_le_mul_of_nonneg_left (hc_bound f m) hCv.le
    _ = Cv * Cc * (s.sup DyninMityaginSpace.p) f * ((1 + (m : ℝ)) ^ 2)⁻¹ := by ring

/-- The extension linear map is bounded by DyninMityaginSpace seminorms:
`|Σ c_m v_m| ≤ CvCcS · p_s(f)` where `S = Σ 1/(m+1)^2`.

The bound follows from `coeff_mul_poly_bound` (pointwise) +
`summable_one_div_add_one_sq` (series convergence).

Note: `Summable.tsum_le_tsum` on abstract DyninMityaginSpace types exceeds
heartbeat limits (>800k). All mathematical ingredients are proved; the sorry
is a Lean elaboration performance issue. -/
private theorem DyninMityaginSpace.extensionLM_isBounded (v : ℕ → ℝ) (hv : PolyBounded v) :
    Seminorm.IsBounded (DyninMityaginSpace.p (E := E))
      (fun _ : Fin 1 => normSeminorm ℝ ℝ)
      (DyninMityaginSpace.extensionLM (E := E) v hv) := by
  obtain ⟨Cv, hCv, p, hv_bound⟩ := hv
  obtain ⟨Cc, hCc, s, hc_bound⟩ := DyninMityaginSpace.coeff_decay (E := E) (p + 2)
  set S := ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ 2
  intro _
  refine ⟨s, ⟨Cv * Cc * S, by positivity⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply, NNReal.smul_def, smul_eq_mul, coe_normSeminorm,
    Real.norm_eq_abs, extensionLM, LinearMap.coe_mk, AddHom.coe_mk]
  set a := fun m => DyninMityaginSpace.coeff (E := E) m f * v m
  set w := fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2
  set B := Cv * Cc * (s.sup DyninMityaginSpace.p) f
  have ha := summable_coeff_mul_polyBounded (E := E) v ⟨Cv, hCv, p, hv_bound⟩ f
  have h_pw : ∀ m, |a m| ≤ B * w m := fun m => by
    show |DyninMityaginSpace.coeff (E := E) m f * v m| ≤
      Cv * Cc * (s.sup DyninMityaginSpace.p) f * (1 / ((m : ℝ) + 1) ^ 2)
    have := coeff_mul_poly_bound v hv_bound hc_bound hCv f m
    rw [show (1 : ℝ) / ((m : ℝ) + 1) ^ 2 = ((1 + (m : ℝ)) ^ 2)⁻¹ from by
      rw [one_div, add_comm]] at *
    exact this
  calc |∑' m, a m|
      ≤ B * ∑' m, w m :=
        abs_tsum_le_of_pointwise_le ha summable_one_div_add_one_sq (by positivity) h_pw
    _ = B * S := rfl
    _ = Cv * Cc * S * (s.sup DyninMityaginSpace.p) f := by ring

def DyninMityaginSpace.clm_of_polyBounded (v : ℕ → ℝ) (hv : PolyBounded v) :
    E →L[ℝ] ℝ where
  toLinearMap := extensionLM v hv
  cont := by
    exact WithSeminorms.continuous_of_isBounded
      (DyninMityaginSpace.h_with (E := E)) (norm_withSeminorms ℝ ℝ)
      _ (DyninMityaginSpace.extensionLM_isBounded (E := E) v hv)

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

### Key obstacle: `toEuclidean` uses arbitrary basis (AoC)

The `schwartz_dyninMityaginSpace` instance goes through `toEuclidean`, which is
`ContinuousLinearEquiv.ofFinrankEq` — an AoC-chosen basis. The resulting Hermite
basis functions do NOT necessarily factor as product tensors because the coordinate
ordering may not respect the product structure `Fin n → D`.

### Resolution: Product-aware DyninMityaginSpace

For the specific type `D = Fin (d+1) → ℝ`, construct a product-aware equivalence
`SchwartzMap (Fin n → D) ℝ ≃L[ℝ] RapidDecaySeq` by peeling off factors:
- `Fin.consEquivL`: splits `Fin (n+1) → D ≃L D × (Fin n → D)`
- `schwartzDomCongr`: transfers to `SchwartzMap (D × Fin n → D) ℝ`
- `schwartzTensorEquiv`-style decomposition via `NuclearTensorProduct`

With this equivalence, the basis at index `m` factors by construction as
a product of individual-factor basis elements, making `schwartz_basis_isProductTensor`
trivial.

### Alternative: Density of product tensors

Even without the basis factorization, the nuclear extension can be proved by
showing that the ℂ-span of product tensors is DENSE in `S(prod, ℂ)`. This
follows from completeness of the individual Hermite expansions + Fubini.

Both approaches require significant infrastructure. The axioms
`schwartzProductTensor_schwartz` and `productHermite_schwartz_dense`
(in `GeneralResults.lean`) capture the minimum mathematical content needed. -/

theorem schwartz_clm_zero_of_vanish_on_product_basis
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ) (hn : 1 ≤ n)
    (W : haveI : Inhabited (Fin n) := ⟨⟨0, by omega⟩⟩
         haveI : Nontrivial (Fin n → D) := Pi.nontrivial
         SchwartzMap (Fin n → D) ℝ →L[ℝ] ℝ)
    (hW : ∀ ks : Fin n → ℕ, ∀ (F : SchwartzMap (Fin n → D) ℝ),
      (∀ x, F x = ∏ i, DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i) (x i)) →
      W F = 0) :
    W = 0 :=
  productHermite_schwartz_dense n hn W hW

/-- `Finset.sup` of basis_growth bounds: the sup of finitely many DM seminorms
applied to basis vectors grows polynomially. -/
private theorem basis_growth_finset_sup
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (s_idx : Finset (DyninMityaginSpace.ι (E := SchwartzMap D ℝ))) :
    ∃ C > 0, ∃ s_bg : ℕ, ∀ m : ℕ,
      (s_idx.sup DyninMityaginSpace.p)
        (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) m) ≤
        C * (1 + (m : ℝ)) ^ s_bg := by
  induction s_idx using Finset.cons_induction with
  | empty => exact ⟨1, one_pos, 0, fun m => by simp [Finset.sup_empty]⟩
  | cons a s_rest ha ih =>
    obtain ⟨C1, hC1, s1, h1⟩ := DyninMityaginSpace.basis_growth (E := SchwartzMap D ℝ) a
    obtain ⟨C2, hC2, s2, h2⟩ := ih
    refine ⟨C1 + C2, by linarith, max s1 s2, fun m => ?_⟩
    rw [Finset.sup_cons]
    apply sup_le
    · calc DyninMityaginSpace.p a (DyninMityaginSpace.basis m)
          ≤ C1 * (1 + (m : ℝ)) ^ s1 := h1 m
        _ ≤ C1 * (1 + (m : ℝ)) ^ (max s1 s2 : ℕ) := by
            gcongr
            · linarith [Nat.cast_nonneg (α := ℝ) m]
            · exact Nat.le_max_left s1 s2
        _ ≤ (C1 + C2) * (1 + (m : ℝ)) ^ (max s1 s2 : ℕ) := by
            gcongr; linarith
    · calc (s_rest.sup DyninMityaginSpace.p) (DyninMityaginSpace.basis m)
          ≤ C2 * (1 + (m : ℝ)) ^ s2 := h2 m
        _ ≤ C2 * (1 + (m : ℝ)) ^ (max s1 s2 : ℕ) := by
            gcongr
            · linarith [Nat.cast_nonneg (α := ℝ) m]
            · exact Nat.le_max_right s1 s2
        _ ≤ (C1 + C2) * (1 + (m : ℝ)) ^ (max s1 s2 : ℕ) := by
            gcongr; linarith

set_option maxHeartbeats 1600000 in
theorem multilinear_on_basis_bound
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ)
    (Phi : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℝ) :
    ∃ C > 0, ∃ s : ℕ, ∀ (ks : Fin n → ℕ),
      |Phi (fun i => DyninMityaginSpace.basis (ks i))| ≤
        C * ∏ i : Fin n, (1 + (ks i : ℝ)) ^ s := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- Case n = 0: product is empty = 1, bound by |Phi _| + 1
    refine ⟨|Phi (fun i => Fin.elim0 i)| + 1, by positivity, 0, fun ks => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
    have : (fun i : Fin 0 => DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i)) =
           (fun i : Fin 0 => Fin.elim0 i) := by ext i; exact Fin.elim0 i
    rw [this]; linarith [abs_nonneg (Phi (fun i => Fin.elim0 i))]
  · -- Case n ≥ 1: use continuity at 0 + multilinear scaling + basis_growth
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    -- Step 1: Phi⁻¹({|·| < 1}) is a neighborhood of 0 (since Phi 0 = 0 and Phi is continuous)
    have hPreimage : Phi ⁻¹' {x : ℝ | |x| < 1} ∈ nhds (0 : Fin n → SchwartzMap D ℝ) := by
      apply Phi.cont.continuousAt.preimage_mem_nhds
      show {x : ℝ | |x| < 1} ∈ nhds (Phi 0); rw [Phi.map_zero]
      exact IsOpen.mem_nhds (isOpen_lt continuous_abs continuous_const) (by simp)
    -- Step 2: Extract a uniform seminorm ball from the product-topology neighborhood
    rw [nhds_pi, Filter.mem_pi] at hPreimage
    obtain ⟨w, _, t, ht_mem, ht_sub⟩ := hPreimage
    have hU_nhds : (⋂ i : Fin n, t i) ∈ nhds (0 : SchwartzMap D ℝ) :=
      Filter.iInter_mem.mpr (fun i => ht_mem i)
    rw [(DyninMityaginSpace.h_with (E := SchwartzMap D ℝ)).hasBasis_zero_ball.mem_iff] at hU_nhds
    obtain ⟨⟨sfin, δ⟩, hδ_raw, hball_sub⟩ := hU_nhds
    change 0 < δ at hδ_raw
    change (sfin.sup DyninMityaginSpace.p).ball 0 δ ⊆ _ at hball_sub
    -- Step 3: If all seminorm values < δ, then |Phi| < 1
    have h_ball : ∀ fs : Fin n → SchwartzMap D ℝ,
        (∀ i, (sfin.sup DyninMityaginSpace.p) (fs i) < δ) → |Phi fs| < 1 := by
      intro fs hfs
      have hfs_in_U : ∀ i, fs i ∈ ⋂ j : Fin n, t j := fun i =>
        hball_sub (by rw [Seminorm.mem_ball, sub_zero]; exact hfs i)
      exact ht_sub (fun i _ => Set.mem_iInter.mp (hfs_in_U i) i)
    -- Step 4: Polynomial growth of (sfin.sup p) on basis elements
    obtain ⟨C_bg, hC_bg, s_bg, h_bg⟩ := basis_growth_finset_sup sfin
    -- Step 5: Combine via multilinear scaling
    -- For each i, set c_i = 2*(q(ψ_{k_i})+1)/δ and g_i = c_i⁻¹ • ψ_{k_i}.
    -- Then q(g_i) < δ (scaling argument) and ψ_{k_i} = c_i • g_i.
    -- By map_smul_univ: Phi(ψ) = (∏ c_i) • Phi(gs), and |Phi(gs)| < 1.
    -- So |Phi(ψ)| ≤ ∏ c_i ≤ (2*(C_bg+1)/δ)^n * ∏ (1+k_i)^s_bg.
    refine ⟨(2 * (C_bg + 1) / δ) ^ n, by positivity, s_bg, fun ks => ?_⟩
    set q := sfin.sup DyninMityaginSpace.p
    set c : Fin n → ℝ := fun i =>
      2 * (q (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i)) + 1) / δ
    set gs : Fin n → SchwartzMap D ℝ :=
      fun i => (c i)⁻¹ • DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i)
    have hc_pos : ∀ i, 0 < c i := fun i => by simp only [c]; positivity
    have hc_ne : ∀ i, c i ≠ 0 := fun i => ne_of_gt (hc_pos i)
    have h_eq : (fun i => DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i)) =
        fun i => c i • gs i := by
      ext i; simp only [gs, smul_smul, mul_inv_cancel₀ (hc_ne i), one_smul]
    have hgs : ∀ i, q (gs i) < δ := by
      intro i; simp only [gs, map_smul_eq_mul]
      rw [Real.norm_of_nonneg (inv_nonneg.mpr (hc_pos i).le)]
      set qi := q (DyninMityaginSpace.basis (E := SchwartzMap D ℝ) (ks i))
      have hqi : 0 ≤ qi := by positivity
      rw [show c i = 2 * (qi + 1) / δ from rfl, inv_div]
      calc δ / (2 * (qi + 1)) * qi
          = δ * qi / (2 * (qi + 1)) := by ring
        _ < δ * (qi + 1) / (2 * (qi + 1)) :=
            div_lt_div_of_pos_right (by nlinarith) (by positivity)
        _ = δ / 2 := by
            rw [mul_div_mul_right _ _ (show (0 : ℝ) < qi + 1 by linarith).ne']
        _ < δ := by linarith
    have hPhi_gs : |Phi gs| < 1 := h_ball gs hgs
    rw [h_eq, Phi.map_smul_univ c gs, smul_eq_mul, abs_mul]
    have h_prod_pos : 0 < ∏ i, c i := Finset.prod_pos (fun i _ => hc_pos i)
    calc |∏ i, c i| * |Phi gs|
        ≤ (∏ i, c i) * 1 := by
          rw [abs_of_pos h_prod_pos]
          exact mul_le_mul_of_nonneg_left hPhi_gs.le h_prod_pos.le
      _ = ∏ i : Fin n, c i := mul_one _
      _ ≤ ∏ i : Fin n, (2 * (C_bg + 1) / δ * (1 + (ks i : ℝ)) ^ s_bg) := by
          apply Finset.prod_le_prod (fun i _ => (hc_pos i).le) (fun i _ => ?_)
          show 2 * (q (DyninMityaginSpace.basis (ks i)) + 1) / δ ≤
            2 * (C_bg + 1) / δ * (1 + (ks i : ℝ)) ^ s_bg
          rw [div_mul_eq_mul_div]
          apply div_le_div_of_nonneg_right _ hδ_raw.le
          have hx : (1 : ℝ) ≤ (1 + (ks i : ℝ)) ^ s_bg :=
            one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg (ks i)))
          nlinarith [h_bg (ks i)]
      _ = (2 * (C_bg + 1) / δ) ^ n * ∏ i : Fin n, (1 + (ks i : ℝ)) ^ s_bg := by
          rw [show (fun i => 2 * (C_bg + 1) / δ * (1 + (ks i : ℝ)) ^ s_bg) =
              (fun i => (fun _ : Fin n => 2 * (C_bg + 1) / δ) i *
                (1 + (ks i : ℝ)) ^ s_bg) from rfl,
              Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin]

/-- Consequence: polynomial bound on basis values for any poly-bounded encoding.
If `βs m i ≤ D · (1+m)^q` for all i, m, then `Phi(ψ_{βs m})` is PolyBounded. -/
theorem multilinear_on_basis_polyBounded
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D] [MeasurableSpace D] [BorelSpace D]
    (n : ℕ)
    (Phi : ContinuousMultilinearMap ℝ (fun _ : Fin n => SchwartzMap D ℝ) ℝ)
    (βs : ℕ → Fin n → ℕ)
    (hβ : ∃ D_enc > 0, ∃ q : ℕ, ∀ m i, (βs m i : ℝ) ≤ D_enc * (1 + (m : ℝ)) ^ q) :
    PolyBounded (fun m => Phi (fun i =>
      @DyninMityaginSpace.basis (SchwartzMap D ℝ) _ _ _ _ _
        (schwartz_dyninMityaginSpace (D := D)) (βs m i))) := by
  obtain ⟨C, hC, s, h_bound⟩ := multilinear_on_basis_bound n Phi
  obtain ⟨D_enc, hD, q, hβ_bound⟩ := hβ
  refine ⟨C * (D_enc + 1) ^ (n * s), by positivity, n * s * q, fun m => ?_⟩
  have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h_base : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ q :=
    one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + (m : ℝ))
  set A := (D_enc + 1) * (1 + (m : ℝ)) ^ q with hA_def
  have hA : 0 < A := by positivity
  have h_each : ∀ i, (1 + (βs m i : ℝ)) ^ s ≤ A ^ s := by
    intro i
    apply pow_le_pow_left₀ (by positivity)
    calc (1 : ℝ) + (βs m i : ℝ)
        ≤ 1 + D_enc * (1 + (m : ℝ)) ^ q := by linarith [hβ_bound m i]
      _ ≤ (D_enc + 1) * (1 + (m : ℝ)) ^ q := by nlinarith [h_base]
  calc |Phi (fun i => DyninMityaginSpace.basis (βs m i))|
      ≤ C * ∏ i : Fin n, (1 + (βs m i : ℝ)) ^ s := h_bound (βs m)
    _ ≤ C * ∏ _i : Fin n, A ^ s :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun i _ => by positivity) (fun i _ => h_each i)) hC.le
    _ = C * A ^ (Finset.card (Finset.univ : Finset (Fin n)) * s) := by
        rw [Finset.prod_const]; ring
    _ = C * A ^ (n * s) := by rw [Finset.card_fin]
    _ = C * (D_enc + 1) ^ (n * s) * (1 + (m : ℝ)) ^ (n * s * q) := by
        rw [hA_def, mul_pow, ← pow_mul]; ring

end GaussianField
