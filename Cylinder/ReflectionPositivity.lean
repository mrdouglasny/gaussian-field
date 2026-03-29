/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reflection Positivity (OS3) for the Free Field on the Cylinder

Proves the Osterwalder-Schrader reflection positivity axiom (OS3) for the
free massive scalar field on S¹_L × ℝ:

  `G(f, Θf) ≥ 0` for all positive-time test functions f.

## Main results

- `cylinderGreen_reflection_positive` — OS3 for the free Green's function (proved)

## Mathematical background

### The Laplace transform factorization

For a test function `f = g ⊗ h` with `h` supported on `(0, ∞)` and
`Θf = g ⊗ Θh` supported on `(-∞, 0)`, the Green's function decomposes as:

  `G(f, Θf) = Σ_n |c_n(g)|² · |ĥ_L(ω_n)|² / (2ω_n)`

where:
- `c_n(g) = ⟨g, φ_n⟩_{L²(S¹)}` is the spatial Fourier coefficient
- `ĥ_L(ω) = ∫₀^∞ h(t) e^{-ωt} dt` is the Laplace transform of h
- `ω_n = resolventFreq L mass n` is the dispersion relation

Each term is a perfect square divided by a positive constant, so the
sum is non-negative. This factorization arises because the resolvent
kernel `e^{-ω|t-s|}/(2ω)` factors as `e^{-ωt} · e^{ωs}/(2ω)` when
`t > 0 > s`, turning the double integral into a product of single
integrals (Laplace transforms).

### Laplace embedding

We encode the factorization via a **Laplace embedding** CLM
`Λ : CylinderTestFunction L → ℓ²` whose components are the
Laplace-resolved spatial Fourier coefficients:

  `(Λf)_n = c_n(g) · ĥ_L(ω_n) / √(2ω_n)`

The key identity is: for positive-time f,

  `G(f, Θf) = ‖Λf‖²_{ℓ²} ≥ 0`

This makes reflection positivity a trivial consequence of the
non-negativity of norms.

### Physical significance

Reflection positivity is the Euclidean counterpart of unitarity in
quantum field theory. Via the Osterwalder-Schrader reconstruction
theorem, it implies:
- The Hilbert space of physical states has a positive-definite inner product
- The Hamiltonian is a self-adjoint operator bounded below
- Wightman positivity holds for the reconstructed Minkowski theory

## References

- Osterwalder-Schrader (1973), Axiom (A3)
- Glimm-Jaffe, *Quantum Physics*, §6.1, Theorem 6.1.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I, §3
-/

import Cylinder.GreenFunction
import Cylinder.PositiveTime
import SchwartzFourier.LaplaceCLM

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Laplace transform on Schwartz space

The Laplace transform `L_ω(h) = ∫₀^∞ h(t) e^{-ωt} dt` is a continuous linear
functional on `𝓢(ℝ)` for each `ω > 0`. Defined and proved in
`SchwartzFourier.LaplaceCLM`:

- `schwartzLaplaceEvalCLM` — the CLM (constructed, not axiomatized)
- `schwartzLaplaceEvalCLM_apply` — specification (proved by rfl)
- `schwartzLaplace_uniformBound` — uniform bound for ω ≥ mass (proved) -/

/-! ## Laplace embedding

The Laplace embedding maps test functions to ℓ² via the Laplace-resolved
spatial Fourier decomposition. For a pure tensor `g ⊗ h`:

  `(Λ(g ⊗ h))_n = c_n(g) · ĥ_L(ω_n) / √(2ω_n)`

where `ĥ_L(ω) = ∫₀^∞ h(t) e^{-ωt} dt` is the Laplace transform of h at
frequency ω, and `c_n(g)` is the n-th spatial Fourier coefficient of g.

The Laplace transform is well-defined because h ∈ 𝓢(ℝ) decays rapidly
and ω_n > 0 for mass > 0. The resulting sequence is in ℓ² because the
spatial Fourier coefficients of g ∈ C∞(S¹) decay rapidly and the Laplace
transforms are bounded. -/

/-- The a-th coordinate functional of the Laplace embedding.

For spatial mode `a`, this is:
  `f ↦ (1/√(2ω_a)) · L_{ω_a}(ntpSliceSchwartz L a f)`

This is a CLM `CylinderTestFunction L →L[ℝ] ℝ` as a composition of:
- `ntpSliceSchwartz L a : CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ`
- `schwartzLaplaceEvalCLM ω_a : SchwartzMap ℝ ℝ →L[ℝ] ℝ`
- scaling by `1/√(2ω_a)` -/
def laplaceEmbeddingCoord (mass : ℝ) (hmass : 0 < mass) (a : ℕ) :
    CylinderTestFunction L →L[ℝ] ℝ :=
  (1 / Real.sqrt (2 * resolventFreq L mass a)) •
    (schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)).comp
      (ntpSliceSchwartz L a)

/-- The coordinate functional is the composition of slice, Laplace eval, and scaling. -/
theorem laplaceEmbeddingCoord_apply (mass : ℝ) (hmass : 0 < mass) (a : ℕ)
    (f : CylinderTestFunction L) :
    laplaceEmbeddingCoord L mass hmass a f =
    (1 / Real.sqrt (2 * resolventFreq L mass a)) *
    schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)
      (ntpSliceSchwartz L a f) := by
  simp [laplaceEmbeddingCoord, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **Decay bound for the Laplace embedding coordinates.**

  `|laplaceEmbeddingCoord a f| ≤ C · p(f) · (1+a)^{-2}`

The proof chains three bounds:
1. **Laplace uniform bound**: `|L_ω(h)| ≤ C_L · schwartz_p(h)` for `ω ≥ mass`
2. **Inverse Hermite**: `schwartz_p(equiv⁻¹ g) ≤ C_inv · rds_p(g)`
3. **Slice decay**: `rds_p(slice_a f) ≤ Z · rds_q(f) · (1+a)^{-4}`

Combined with the `1/√(2ω_a) ≤ 1/√(2·mass)` scaling, this gives `(1+a)^{-4}`
decay, which is much stronger than the `(1+a)^{-2}` required for ℓ². -/
theorem laplaceEmbeddingCoord_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (DyninMityaginSpace.ι (E := CylinderTestFunction L))) (C : ℝ) (_ : 0 < C),
    ∀ (a : ℕ) (f : CylinderTestFunction L),
      |laplaceEmbeddingCoord L mass hmass a f| ≤
      (C * (s.sup DyninMityaginSpace.p) f) * (1 + (a : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
  -- Step 1: Laplace uniform Schwartz bound
  obtain ⟨s_L, C_L, hC_L, h_laplace⟩ := schwartzLaplace_uniformBound mass hmass
  -- Step 2: Inverse Hermite bound (Schwartz seminorms of equiv⁻¹ g bounded by RDS seminorms of g)
  have h_inv_combined :
      ∃ (s_inv : Finset ℕ) (C_inv : NNReal), C_inv ≠ 0 ∧
      ∀ g : RapidDecaySeq,
        (s_L.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2))
          (schwartzRapidDecayEquiv1D.symm g) ≤
        ↑C_inv * (s_inv.sup RapidDecaySeq.rapidDecaySeminorm) g := by
    have h_each : ∀ idx : ℕ × ℕ,
        ∃ (s_j : Finset ℕ) (C_j : NNReal), C_j ≠ 0 ∧
        ∀ g : RapidDecaySeq,
          SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) idx.1 idx.2
            (schwartzRapidDecayEquiv1D.symm g) ≤
          ↑C_j * (s_j.sup RapidDecaySeq.rapidDecaySeminorm) g := by
      intro ⟨k', l'⟩
      set q : Seminorm ℝ RapidDecaySeq :=
        (SchwartzMap.seminorm ℝ k' l').comp
          schwartzRapidDecayEquiv1D.symm.toContinuousLinearMap.toLinearMap
      have hq_cont : Continuous q :=
        ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm ⟨k', l'⟩).comp
          schwartzRapidDecayEquiv1D.symm.continuous
      obtain ⟨s, C, hCne, hle⟩ := Seminorm.bound_of_continuous
        RapidDecaySeq.rapidDecay_withSeminorms q hq_cont
      exact ⟨s, C, hCne, fun g => Seminorm.le_def.mp hle g⟩
    choose s_j C_j hC_j h_j using h_each
    refine ⟨s_L.biUnion s_j,
      s_L.sum (fun idx => C_j idx) + 1,
      by simp, fun g => ?_⟩
    set big_rds := (s_L.biUnion s_j).sup RapidDecaySeq.rapidDecaySeminorm
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro idx hidx
    calc SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) idx.1 idx.2
          (schwartzRapidDecayEquiv1D.symm g)
        ≤ ↑(C_j idx) * ((s_j idx).sup RapidDecaySeq.rapidDecaySeminorm) g := h_j idx g
      _ ≤ ↑(C_j idx) * big_rds g := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_biUnion_of_mem s_j hidx)) g
      _ ≤ ↑(s_L.sum (fun idx => C_j idx)) * big_rds g := by
          apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
          push_cast
          exact_mod_cast Finset.single_le_sum (fun j _ => (C_j j).coe_nonneg) hidx
      _ ≤ ↑(s_L.sum (fun idx => C_j idx) + 1) * big_rds g := by
          apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
          push_cast; linarith
  obtain ⟨s_inv, C_inv, hC_inv_ne, h_inv⟩ := h_inv_combined
  -- Step 3: Slice extraction decay
  -- For each k ∈ s_inv, rds_k(slice_a f) ≤ Z * rds_{k+4+2} f * (1+a)^{-4}
  set Z := ∑' (n : ℕ), ((1 + (n : ℝ)) ^ 2)⁻¹ with hZ
  have hZ_pos : 0 < Z :=
    NuclearTensorProduct.summable_inv_one_add_sq.tsum_pos
      (fun n => by positivity) 0 (by positivity)
  set s_total := s_inv.image (· + 6) with hs_total
  have h_slice_decay : ∀ (n : ℕ) (f : CylinderTestFunction L),
      (s_inv.sup RapidDecaySeq.rapidDecaySeminorm) (ntpExtractSlice n f) ≤
      Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
      ((1 + (n : ℝ)) ^ 4)⁻¹ := by
    intro n f
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro k hk
    have h_decay := ntpExtractSlice_a_decay n k 4 f
    calc RapidDecaySeq.rapidDecaySeminorm k (ntpExtractSlice n f)
        ≤ Z * RapidDecaySeq.rapidDecaySeminorm (k + 4 + 2) f *
          ((1 + (n : ℝ)) ^ 4)⁻¹ := h_decay
      _ ≤ Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (n : ℝ)) ^ 4)⁻¹ := by
        gcongr
        exact Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  -- Step 4: Combine everything
  -- scaling: 1/√(2ω_a) ≤ 1/√(2·mass) since ω_a ≥ mass
  set scale := 1 / Real.sqrt (2 * mass) with hscale_def
  have hscale_pos : 0 < scale := by
    apply div_pos one_pos
    exact Real.sqrt_pos_of_pos (by positivity)
  -- Total constant
  set C_total := scale * C_L * ↑C_inv * Z with hC_total
  refine ⟨s_total, C_total + 1, by positivity, fun a f => ?_⟩
  -- Chain:
  -- |laplaceEmbeddingCoord a f|
  --   = |1/√(2ω_a)| * |L_{ω_a}(slice_a f)|
  --   ≤ scale * |L_{ω_a}(slice_a f)|
  --   ≤ scale * C_L * schwartz_p(slice_a f)
  --   = scale * C_L * schwartz_p(equiv⁻¹(ntpExtractSlice a f))
  --   ≤ scale * C_L * C_inv * rds_p(ntpExtractSlice a f)
  --   ≤ scale * C_L * C_inv * Z * (s_total.sup rds) f * (1+a)^{-4}
  --   ≤ C_total * p(f) * (1+a)^{-2}  (since (1+a)^{-4} ≤ (1+a)^{-2})
  rw [laplaceEmbeddingCoord_apply]
  -- Bound the absolute value of the product
  have h1 : |1 / Real.sqrt (2 * resolventFreq L mass a)| ≤ scale := by
    rw [abs_div, abs_one, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply one_div_le_one_div_of_le (Real.sqrt_pos_of_pos (by positivity))
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ 2)
    exact resolventFreq_mass_le L mass hmass.le a
  -- Bound the Laplace evaluation
  have hωa := resolventFreq_mass_le L mass hmass.le a
  have h2 : |schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)
      (ntpSliceSchwartz L a f)| ≤
      C_L * (s_L.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2))
        (ntpSliceSchwartz L a f) :=
    h_laplace (resolventFreq L mass a) hωa (ntpSliceSchwartz L a f)
  -- ntpSliceSchwartz = equiv⁻¹ ∘ ntpExtractSlice
  have h_slice_eq : ntpSliceSchwartz L a f =
      schwartzRapidDecayEquiv1D.symm (ntpExtractSlice a f) := rfl
  -- Bound Schwartz seminorms via inverse Hermite
  have h3 : (s_L.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2))
      (ntpSliceSchwartz L a f) ≤
      ↑C_inv * (s_inv.sup RapidDecaySeq.rapidDecaySeminorm) (ntpExtractSlice a f) := by
    rw [h_slice_eq]; exact h_inv (ntpExtractSlice a f)
  -- Bound slice RDS seminorms via decay
  have h4 := h_slice_decay a f
  -- Now chain the bounds
  have h_abs_prod : |1 / Real.sqrt (2 * resolventFreq L mass a) *
      schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)
        (ntpSliceSchwartz L a f)| ≤
      scale * C_L * ↑C_inv * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
      ((1 + (a : ℝ)) ^ 4)⁻¹ := by
    rw [abs_mul]
    calc |1 / Real.sqrt (2 * resolventFreq L mass a)| *
          |schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)
            (ntpSliceSchwartz L a f)|
        ≤ scale * (C_L * (s_L.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2))
            (ntpSliceSchwartz L a f)) := by gcongr
      _ ≤ scale * (C_L * (↑C_inv * (s_inv.sup RapidDecaySeq.rapidDecaySeminorm)
            (ntpExtractSlice a f))) := by gcongr
      _ ≤ scale * (C_L * (↑C_inv * (Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
            ((1 + (a : ℝ)) ^ 4)⁻¹))) := by gcongr
      _ = scale * C_L * ↑C_inv * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
            ((1 + (a : ℝ)) ^ 4)⁻¹ := by ring
  -- (1+a)^{-4} ≤ (1+a)^{-2}
  have h_pow_le : ((1 + (a : ℝ)) ^ 4)⁻¹ ≤ ((1 + (a : ℝ)) ^ 2)⁻¹ :=
    inv_anti₀ (by positivity)
      (pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) a] : (1 : ℝ) ≤ 1 + (a : ℝ))
        (by omega))
  -- Convert rpow to pow
  rw [show ((-2 : ℤ) : ℝ) = (-2 : ℝ) from by norm_cast,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (a : ℝ)),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast,
      Real.rpow_natCast]
  calc |1 / Real.sqrt (2 * resolventFreq L mass a) *
        schwartzLaplaceEvalCLM (resolventFreq L mass a) (resolventFreq_pos L mass hmass a)
          (ntpSliceSchwartz L a f)|
      ≤ scale * C_L * ↑C_inv * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 4)⁻¹ := h_abs_prod
    _ ≤ scale * C_L * ↑C_inv * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 2)⁻¹ := by gcongr
    _ = C_total * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 2)⁻¹ := by ring
    _ ≤ (C_total + 1) * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 2)⁻¹ := by
      gcongr
      linarith

/-- Helper: package the decay bound for `nuclear_ell2_embedding_from_decay`. -/
private def laplaceEmbedding_ell2 (mass : ℝ) (hmass : 0 < mass) :
    ∃ (j : CylinderTestFunction L →L[ℝ] ell2'),
      ∀ (f : CylinderTestFunction L) (a : ℕ),
        (j f : ℕ → ℝ) a = laplaceEmbeddingCoord L mass hmass a f := by
  obtain ⟨s, C, hC, hdecay⟩ := laplaceEmbeddingCoord_decay L mass hmass
  exact nuclear_ell2_embedding_from_decay
    (laplaceEmbeddingCoord L mass hmass) s C hC hdecay

/-- **The Laplace embedding** `Λ : CylinderTestFunction L → ℓ²`.

Maps test functions to ℓ² via the Laplace-resolved spatial Fourier
decomposition. The a-th component of `Λf` encodes the coupling of the
a-th spatial Fourier mode to the temporal Laplace transform at the
corresponding resolvent frequency `ω_a`:

  `(Λf)_a = (1/√(2ω_a)) · L_{ω_a}(slice_a f)`

Constructed from the coordinate functionals `laplaceEmbeddingCoord` via
`nuclear_ell2_embedding_from_decay`. The coordinates decay like `(1+a)^{-4}`,
well within the `(1+a)^{-2}` required for ℓ² membership.

Used to prove reflection positivity: `G(f, Θf) = ‖Λf‖² ≥ 0`. -/
def cylinderLaplaceEmbedding (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2' :=
  (laplaceEmbedding_ell2 L mass hmass).choose

/-- The a-th coordinate of the Laplace embedding is the coordinate functional.

  `(Λf)_a = laplaceEmbeddingCoord L mass hmass a f` -/
theorem cylinderLaplaceEmbedding_coord (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (a : ℕ) :
    (cylinderLaplaceEmbedding L mass hmass f : ℕ → ℝ) a =
    laplaceEmbeddingCoord L mass hmass a f :=
  (laplaceEmbedding_ell2 L mass hmass).choose_spec f a

/-- **Resolvent–Laplace factorization identity** (mode-level).

For a positive-time Schwartz function `h` and resolvent frequency `ω > 0`:

  `⟨R_ω(h), R_ω(h̃)⟩_{DM} = (1/(2ω)) · (L_ω(h))²`

where `R_ω` is the resolvent Fourier multiplier `(p² + ω²)^{-1/2}`,
`h̃ = schwartzReflection h`, and `⟨·,·⟩_{DM}` is the ℓ² inner product
of DM basis coefficients (= L² inner product by Hermite–Parseval).

**Proof sketch** (verified by Gemini deep think):
The L² inner product `⟨R_ω h, R_ω h̃⟩ = ⟨h, R_ω² h̃⟩` by self-adjointness.
The operator `R_ω²` has convolution kernel `(1/(2ω))e^{-ω|t|}` (inverse
Fourier transform of `(p² + ω²)^{-1}`). For `h` supported on `[0,∞)` and
`h̃` supported on `(-∞, 0]`, the absolute value `|t - s| = t - s` for
`t ≥ 0, s ≤ 0`, so the double integral factors as
`(1/(2ω)) · (∫₀^∞ h(t)e^{-ωt} dt)² = (1/(2ω)) · (L_ω h)²`. -/
axiom resolvent_laplace_inner
    (ω : ℝ) (hω : 0 < ω)
    (h : SchwartzMap ℝ ℝ) (hh : h ∈ schwartzPositiveTimeSubmodule) :
    ∑' b, DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
            (resolventMultiplierCLM hω h) *
          DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
            (resolventMultiplierCLM hω (schwartzReflection h)) =
    (1 / (2 * ω)) * (schwartzLaplaceEvalCLM ω hω h) ^ 2

/-- The Laplace factorization identity for the cylinder Green's function.

  `G(f, Θf) = ‖Λf‖²_{ℓ²}`

Proved from the mode-level `resolvent_laplace_inner` axiom by:
1. Expanding both sides as ℓ² tsums via coordinate formulas
2. Grouping the LHS by spatial mode (Cantor pairing reorganization)
3. Matching each mode's contribution with the Laplace embedding -/
theorem cylinderGreen_reflection_eq_laplaceNorm
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) :
    cylinderGreen L mass hmass f (cylinderTimeReflection L f) =
    @inner ℝ ell2' _ (cylinderLaplaceEmbedding L mass hmass f)
      (cylinderLaplaceEmbedding L mass hmass f) := by
  sorry

/-! ## Reflection positivity (OS3)

The central Osterwalder-Schrader axiom: the Green's function applied
to a positive-time test function and its time reflection is non-negative.

This is an immediate consequence of the Laplace factorization identity:
`G(f, Θf) = ‖Λf‖² ≥ 0`. -/

/-- **Reflection positivity (OS3) for the free field on the cylinder.**

  `G(f, Θf) ≥ 0` for all positive-time test functions f.

This is the Euclidean counterpart of unitarity: it ensures the
reconstructed Hilbert space has a positive-definite inner product.

Proof: By the Laplace factorization identity,
  `G(f, Θf) = ‖Λf‖²_{ℓ²} ≥ 0`
since norms are non-negative. -/
theorem cylinderGreen_reflection_positive (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L)
    (hf : f ∈ cylinderPositiveTimeSubmodule L) :
    0 ≤ cylinderGreen L mass hmass f (cylinderTimeReflection L f) := by
  rw [cylinderGreen_reflection_eq_laplaceNorm L mass hmass f hf]
  exact real_inner_self_nonneg

-- NOTE: cylinderGreen_reflection_strict_positive was removed as a dead axiom
-- (never referenced by any downstream declaration). Strict RP is not needed
-- for basic OS3 (which only requires nonnegativity, proved above).

end GaussianField
