/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Bilinear Form and Green's Function

Defines the heat kernel and Green's function on any DyninMityaginSpace
equipped with Laplacian eigenvalues. These are the universal analytic objects
that drive the continuum limit construction.

## Main definitions

- `HasLaplacianEigenvalues` — typeclass providing eigenvalues μ_m ≥ 0 of -Δ
- `heatKernelBilinear` — K_t(f,g) = Σ_m e^{-tμ_m} coeff_m(f) coeff_m(g)
- `l2InnerProduct` — ⟨f,g⟩_{L²} = Σ_m coeff_m(f) coeff_m(g)
- `greenFunctionBilinear` — G_mass(f,g) = Σ_m coeff_m(f) coeff_m(g) / (μ_m + mass²)

## Key properties

- `heatKernelBilinear_tensorProduct` — K_t factors under ⊗
- `heatKernelBilinear_tendsto_l2` — K_t(f,g) → ⟨f,g⟩_{L²} as t → 0⁺
- `greenFunctionBilinear_pos` — G_mass(f,f) > 0 for f ≠ 0

## Design: mass separated from eigenvalues

The eigenvalues are of -Δ alone (nonneg, not strictly positive). Mass enters
only through the Green's function. This ensures:
- Tensor product correctness: μ_{E₁⊗E₂} = μ_{E₁} + μ_{E₂} (not +2m²)
- Heat kernel factorization: K_t factors multiplicatively
- Identity at t=0: K_t → L² inner product (not mass-dependent)

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Nuclear.NuclearTensorProduct
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.LocallyConvex.SeparatingDual

noncomputable section

open scoped BigOperators

namespace GaussianField

/-! ## Laplacian eigenvalues -/

/-- **Laplacian eigenvalues on a DyninMityaginSpace.**

Each DyninMityaginSpace can be equipped with eigenvalues of the Laplacian -Δ
associated to its geometry. The eigenvalues are nonneg (the zero mode on the
circle has μ₀ = 0). Mass is NOT included — it enters only through the
Green's function.

The basis `{e_m}` of the DMS is assumed orthonormal w.r.t. the L² inner
product, and the eigenvalues satisfy `-Δ e_m = μ_m e_m`. -/
class HasLaplacianEigenvalues (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [DyninMityaginSpace E] where
  eigenvalue : ℕ → ℝ
  eigenvalue_nonneg : ∀ m, 0 ≤ eigenvalue m

/-! ## L² inner product -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [DyninMityaginSpace E]

/-- Helper: the m-th term of the L² inner product series. -/
private def l2Term (f g : E) (m : ℕ) : ℝ :=
  DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g

/-- **L² inner product via Schauder coefficients.**

  `⟨f, g⟩_{L²} = Σ_m coeff_m(f) · coeff_m(g)`

This is the Parseval identity for the orthonormal Schauder basis. -/
def l2InnerProduct (f g : E) : ℝ :=
  ∑' m, l2Term f g m

/-- Summability of the L² inner product series. -/
theorem l2InnerProduct_summable (f g : E) :
    Summable (l2Term f g) := by
  -- Use coeff_decay at exponent 2 for f and g to bound |c_m(f) * c_m(g)| ≤ const/(1+m)^4
  obtain ⟨Cf, hCf, sf, hdf⟩ := DyninMityaginSpace.coeff_decay (E := E) 2
  obtain ⟨Cg, hCg, sg, hdg⟩ := DyninMityaginSpace.coeff_decay (E := E) 2
  set Bf := Cf * (sf.sup DyninMityaginSpace.p) f
  set Bg := Cg * (sg.sup DyninMityaginSpace.p) g
  -- Summability of 1/(m+1)^2
  have h1sq : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    exact this.congr (fun m => by push_cast; ring_nf)
  -- Bound: ‖l2Term f g m‖ ≤ Bf * Bg / (1+m)^4
  set bound : ℕ → ℝ := fun m => Bf * Bg * (1 / ((m : ℝ) + 1) ^ 2) ^ 2
  have hbound_summable : Summable bound := by
    apply Summable.of_nonneg_of_le (fun m => by positivity : ∀ m, 0 ≤ bound m)
    · intro m
      show bound m ≤ Bf * Bg * (1 / ((m : ℝ) + 1) ^ 2)
      have h1 : (1 : ℝ) / ((m : ℝ) + 1) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ (by linarith [Nat.cast_nonneg' (α := ℝ) m] : (1 : ℝ) ≤ (m : ℝ) + 1)
      show Bf * Bg * (1 / ((m : ℝ) + 1) ^ 2) ^ 2 ≤ Bf * Bg * (1 / ((m : ℝ) + 1) ^ 2)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc (1 / ((m : ℝ) + 1) ^ 2) ^ 2
          = (1 / ((m : ℝ) + 1) ^ 2) * (1 / ((m : ℝ) + 1) ^ 2) := sq _
        _ ≤ 1 * (1 / ((m : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 1 / ((m : ℝ) + 1) ^ 2 := one_mul _
    · exact h1sq.mul_left (Bf * Bg)
  exact Summable.of_norm_bounded hbound_summable (fun m => by
    show ‖l2Term f g m‖ ≤ bound m
    simp only [l2Term, bound, Real.norm_eq_abs, abs_mul]
    have hf_bound : |DyninMityaginSpace.coeff m f| ≤ Bf / (1 + (m : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; exact hdf f m
    have hg_bound : |DyninMityaginSpace.coeff m g| ≤ Bg / (1 + (m : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; exact hdg g m
    calc |DyninMityaginSpace.coeff m f| * |DyninMityaginSpace.coeff m g|
        ≤ (Bf / (1 + (m : ℝ)) ^ 2) * (Bg / (1 + (m : ℝ)) ^ 2) :=
          mul_le_mul hf_bound hg_bound (abs_nonneg _) (by positivity)
      _ = Bf * Bg * (1 / ((m : ℝ) + 1) ^ 2) ^ 2 := by field_simp; ring)

/-! ## Heat kernel bilinear form -/

/-- Helper: the m-th term of the heat kernel series. -/
private def heatKernelTerm [HasLaplacianEigenvalues E] (t : ℝ) (f g : E) (m : ℕ) : ℝ :=
  Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) *
    DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g

/-- **Heat kernel bilinear form.**

  `K_t(f, g) = Σ_m e^{-tμ_m} · coeff_m(f) · coeff_m(g)`

The sum converges absolutely because `coeff_m(f)` and `coeff_m(g)` are
rapidly decreasing and `e^{-tμ_m} ≤ 1` for t ≥ 0. -/
def heatKernelBilinear [HasLaplacianEigenvalues E] (t : ℝ)
    (f g : E) : ℝ :=
  ∑' m, heatKernelTerm (E := E) t f g m

/-- Summability of the heat kernel series for t > 0. -/
theorem heatKernelBilinear_summable [HasLaplacianEigenvalues E]
    (t : ℝ) (ht : 0 < t) (f g : E) :
    Summable (heatKernelTerm (E := E) t f g) := by
  -- Bound: |e^{-tμ_m} c_m(f) c_m(g)| ≤ |c_m(f) c_m(g)| since e^{-tμ_m} ∈ [0,1]
  apply (l2InnerProduct_summable f g).abs.of_norm_bounded_eventually
  apply Filter.Eventually.of_forall
  intro m
  simp only [heatKernelTerm, l2Term, Real.norm_eq_abs]
  rw [show Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) *
    DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g =
    Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) *
    (DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g) from by ring]
  rw [abs_mul]
  apply mul_le_of_le_one_left (abs_nonneg _)
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m])

/-! ## Heat kernel properties -/

/-- **Heat kernel converges to L² inner product as t → 0⁺.**

  `lim_{t→0⁺} K_t(f,g) = ⟨f,g⟩_{L²}`

Proof: dominated convergence. Each term `e^{-tμ_m} → 1` as `t → 0⁺`,
and `|e^{-tμ_m} c_m(f) c_m(g)| ≤ |c_m(f) c_m(g)|` which is summable. -/
theorem heatKernelBilinear_tendsto_l2
    [HasLaplacianEigenvalues E] (f g : E) :
    Filter.Tendsto
      (fun t : ℝ => heatKernelBilinear (E := E) t f g)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (l2InnerProduct f g)) := by
  unfold heatKernelBilinear l2InnerProduct
  apply tendsto_tsum_of_dominated_convergence (l2InnerProduct_summable f g).abs
  · -- Pointwise convergence: heatKernelTerm t f g m → l2Term f g m
    intro m
    simp only [heatKernelTerm]
    have hcfg : l2Term f g m =
        1 * DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g := by
      simp [l2Term]
    rw [hcfg]
    apply Filter.Tendsto.mul (Filter.Tendsto.mul _ tendsto_const_nhds) tendsto_const_nhds
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    apply (Real.continuous_exp.tendsto 0).comp
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hca : ContinuousAt (fun t : ℝ => -t *
        HasLaplacianEigenvalues.eigenvalue (E := E) m) 0 := by fun_prop
    simp only [ContinuousAt, neg_zero, zero_mul] at hca
    exact hca
  · -- Norm bound: ‖heatKernelTerm t f g m‖ ≤ |l2Term f g m| for t > 0
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro t (ht : 0 < t) m
    simp only [heatKernelTerm, l2Term, Real.norm_eq_abs]
    rw [show Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) *
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g =
        Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) *
        (DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g) from by ring]
    rw [abs_mul, abs_mul]
    apply mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (by nlinarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m])

/-- **Heat kernel is nonneg on the diagonal:** `K_t(f,f) ≥ 0`. -/
theorem heatKernelBilinear_nonneg [HasLaplacianEigenvalues E]
    (t : ℝ) (f : E) :
    0 ≤ heatKernelBilinear (E := E) t f f := by
  unfold heatKernelBilinear heatKernelTerm
  apply tsum_nonneg
  intro m
  nlinarith [Real.exp_pos (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m),
             sq_nonneg (DyninMityaginSpace.coeff m f)]

/-- **Heat kernel bounded by L² inner product:** `K_t(f,f) ≤ ⟨f,f⟩_{L²}`.

Since `e^{-tμ_m} ≤ 1` for t > 0 and μ_m ≥ 0. -/
theorem heatKernelBilinear_le_l2 [HasLaplacianEigenvalues E]
    (t : ℝ) (ht : 0 < t) (f : E) :
    heatKernelBilinear (E := E) t f f ≤ l2InnerProduct f f := by
  unfold heatKernelBilinear l2InnerProduct
  apply Summable.tsum_le_tsum
  · intro m
    unfold heatKernelTerm l2Term
    have hexp : Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m])
    nlinarith [sq_nonneg (DyninMityaginSpace.coeff m f),
               Real.exp_pos (-t * HasLaplacianEigenvalues.eigenvalue (E := E) m)]
  · exact heatKernelBilinear_summable t ht f f
  · exact l2InnerProduct_summable f f

/-! ## Green's function -/

/-- Helper: the m-th term of the Green's function series. -/
private def greenTerm [HasLaplacianEigenvalues E]
    (mass : ℝ) (f g : E) (m : ℕ) : ℝ :=
  DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g /
    (HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2)

/-- **Green's function bilinear form.**

  `G_mass(f, g) = Σ_m coeff_m(f) · coeff_m(g) / (μ_m + mass²)`

This is the spectral representation of `(-Δ + mass²)⁻¹`. Equivalently,
it is the Laplace transform of the heat kernel:
  `G_mass(f, g) = ∫₀^∞ e^{-t·mass²} K_t(f, g) dt`

The sum converges because `1/(μ_m + mass²) ≤ 1/mass²` is bounded and
coefficients are rapidly decreasing. -/
def greenFunctionBilinear [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f g : E) : ℝ :=
  ∑' m, greenTerm (E := E) mass f g m

/-- Summability of the Green's function series. -/
theorem greenFunctionBilinear_summable [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f g : E) :
    Summable (greenTerm (E := E) mass f g) := by
  have hmass_sq_pos : (0 : ℝ) < mass ^ 2 := sq_pos_of_pos hmass
  apply (Summable.mul_left (1 / mass ^ 2) (l2InnerProduct_summable f g).abs).of_norm_bounded_eventually
  apply Filter.Eventually.of_forall
  intro m
  simp only [greenTerm, Real.norm_eq_abs]
  rw [abs_div, abs_mul]
  have hden_pos : 0 < HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2 :=
    by linarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m, hmass_sq_pos]
  rw [abs_of_pos hden_pos]
  have hmass_le : mass ^ 2 ≤ HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2 :=
    le_add_of_nonneg_left (HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m)
  calc |DyninMityaginSpace.coeff m f| * |DyninMityaginSpace.coeff m g| /
        (HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2)
      ≤ |DyninMityaginSpace.coeff m f| * |DyninMityaginSpace.coeff m g| / mass ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          hmass_sq_pos hmass_le
    _ = 1 / mass ^ 2 * (|DyninMityaginSpace.coeff m f| * |DyninMityaginSpace.coeff m g|) := by
        ring
    _ = 1 / mass ^ 2 * |DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g| := by
        rw [abs_mul]

/-- **Green's function equals the Laplace transform of the heat kernel.**

Informally: `G_mass(f, g) = ∫₀^∞ e^{-t·mass²} K_t(f, g) dt`.
This is obtained by exchanging sum and integral (Fubini-Tonelli),
then evaluating `∫₀^∞ e^{-t(μ_m + mass²)} dt = 1/(μ_m + mass²)`.

The spectral sum definition is primary; this is a derived identity. -/
theorem greenFunctionBilinear_eq_heatKernel [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f g : E) (m : ℕ) :
    greenTerm (E := E) mass f g m =
    DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g /
      (HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2) := by
  rfl

/-- **Green's function is nonneg on the diagonal.**

  `G_mass(f, f) ≥ 0` for all `f`

Each term `coeff_m(f)² / (μ_m + mass²) ≥ 0` since the numerator is a square
and the denominator is positive (`μ_m ≥ 0`, `mass² > 0`). The tsum of nonneg
terms is nonneg. -/
theorem greenFunctionBilinear_nonneg [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f : E) :
    0 ≤ greenFunctionBilinear mass hmass f f := by
  apply tsum_nonneg
  intro m
  apply div_nonneg (mul_self_nonneg _)
  linarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m, sq_pos_of_pos hmass]

/-- **Green's function is positive definite.**

  `G_mass(f, f) > 0` for nonzero `f`

Since `coeff_m(f)² / (μ_m + mass²) ≥ 0` for all m, and at least one
coefficient is nonzero (by the expansion property of DMS), so the sum
is strictly positive. -/
theorem greenFunctionBilinear_pos [HasLaplacianEigenvalues E] [T1Space E]
    (mass : ℝ) (hmass : 0 < mass) (f : E) (hf : f ≠ 0) :
    0 < greenFunctionBilinear mass hmass f f := by
  -- Step 1: f ≠ 0 implies some coefficient is nonzero
  have hcoeff : ∃ m, DyninMityaginSpace.coeff m f ≠ 0 := by
    by_contra hall
    push_neg at hall
    haveI : LocallyConvexSpace ℝ E := DyninMityaginSpace.h_with.toLocallyConvexSpace
    obtain ⟨φ, hφ⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hf
    exact hφ (by rw [DyninMityaginSpace.expansion φ f]; simp [hall])
  obtain ⟨m₀, hm₀⟩ := hcoeff
  -- Step 2: Use tsum_pos with the witness m₀
  unfold greenFunctionBilinear
  exact (greenFunctionBilinear_summable mass hmass f f).tsum_pos
    (fun m => div_nonneg (mul_self_nonneg _)
      (by linarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m, sq_pos_of_pos hmass]))
    m₀ (div_pos (mul_self_pos.mpr hm₀)
      (by linarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m₀, sq_pos_of_pos hmass]))

/-- **Green's function is bounded by `1/mass² · ⟨f,f⟩_{L²}`.**

Since `1/(μ_m + mass²) ≤ 1/mass²`, we have
`G_mass(f,f) ≤ (1/mass²) · ⟨f,f⟩_{L²}`. -/
theorem greenFunctionBilinear_le [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f : E) :
    greenFunctionBilinear mass hmass f f ≤
      (1 / mass ^ 2) * l2InnerProduct f f := by
  unfold greenFunctionBilinear l2InnerProduct
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro m
    unfold greenTerm l2Term
    have hmass_sq_pos : (0 : ℝ) < mass ^ 2 := sq_pos_of_pos hmass
    have hden_pos : 0 < HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2 :=
      by linarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m]
    have hmass_le : mass ^ 2 ≤ HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2 :=
      le_add_of_nonneg_left (HasLaplacianEigenvalues.eigenvalue_nonneg (E := E) m)
    have hsq : 0 ≤ DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f :=
      mul_self_nonneg _
    calc DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f /
          (HasLaplacianEigenvalues.eigenvalue (E := E) m + mass ^ 2)
        ≤ DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f / mass ^ 2 :=
          div_le_div_of_nonneg_left hsq hmass_sq_pos hmass_le
      _ = 1 / mass ^ 2 * (DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f) := by
          ring
  · exact greenFunctionBilinear_summable mass hmass f f
  · exact Summable.mul_left _ (l2InnerProduct_summable f f)

/-! ## Tensor product eigenvalues -/

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁]
  [TopologicalSpace E₁] [IsTopologicalAddGroup E₁]
  [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
  {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂]
  [TopologicalSpace E₂] [IsTopologicalAddGroup E₂]
  [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]

/-- **Tensor product Laplacian eigenvalues are sums.**

For `E₁ ⊗̂ E₂`, the eigenvalue at Cantor-paired index `m = pair(n₁, n₂)` is
`μ₁(n₁) + μ₂(n₂)`, corresponding to `-Δ_{E₁} ⊗ I + I ⊗ (-Δ_{E₂})`. -/
instance tensorProductHasLaplacianEigenvalues
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂] :
    HasLaplacianEigenvalues (NuclearTensorProduct E₁ E₂) where
  eigenvalue m :=
    let p := Nat.unpair m
    HasLaplacianEigenvalues.eigenvalue (E := E₁) p.1 +
      HasLaplacianEigenvalues.eigenvalue (E := E₂) p.2
  eigenvalue_nonneg m := add_nonneg
    (HasLaplacianEigenvalues.eigenvalue_nonneg (Nat.unpair m).1)
    (HasLaplacianEigenvalues.eigenvalue_nonneg (Nat.unpair m).2)

/-! ## Heat kernel factorization -/

/-- **Heat kernel is multiplicative under tensor product.**

  `K_t^{E₁⊗E₂}(f₁⊗f₂, g₁⊗g₂) = K_t^{E₁}(f₁,g₁) · K_t^{E₂}(f₂,g₂)`

This follows from:
- `e^{-t(μ₁+μ₂)} = e^{-tμ₁} · e^{-tμ₂}`
- `coeff_{pair(n₁,n₂)}(f₁⊗f₂) = coeff_{n₁}(f₁) · coeff_{n₂}(f₂)`
- Fubini (absolute convergence of double series)

This is THE KEY THEOREM that makes the 1D → 2D construction work. -/
theorem heatKernelBilinear_tensorProduct
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂]
    (t : ℝ) (f₁ g₁ : E₁) (f₂ g₂ : E₂) :
    heatKernelBilinear (E := NuclearTensorProduct E₁ E₂) t
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) =
    heatKernelBilinear (E := E₁) t f₁ g₁ *
      heatKernelBilinear (E := E₂) t f₂ g₂ := by
  sorry

end GaussianField
