/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Method of Images: Torus-to-Cylinder Green's Function Bound

Establishes the uniform bound on the asymmetric torus Green's function
`G_{Lt,Ls}(f, f)` in terms of the cylinder Green's function `G_{Ls}(f, f)`,
via the **method of images** decomposition.

## Mathematical background

The torus Green's function on `T_{Lt,Ls} = (ℝ/Lt ℤ) × S¹_{Ls}` is related
to the cylinder Green's function on `S¹_{Ls} × ℝ` by periodization in the
time direction:

  `G_{Lt,Ls}(f, f) = G_{Ls}(f, f) + Σ_{k ≠ 0} ∬ f(x) f(y) G_{Ls}(x - y + (kLt, 0)) dx dy`

The cylinder Green's function has a mass gap `m > 0`, giving exponential
decay `G_{Ls}(x) ~ e^{-m|x|}` in the temporal direction. Each wrap-around
term is therefore bounded by `C(f) · e^{-m|k|Lt}`, and the geometric
series sums to give a uniform bound.

## Main results

- `cylinderGreen_continuous_seminorm_bound` — G_{Ls}(f, f) ≤ C · q(f)²
- `l2InnerProduct_periodizeCLM_le` — ℓ² coefficient norm of `periodize_Lt h` bounded by a
  Schwartz seminorm of `h`, uniformly in Lt ≥ 1
- `embed_l2_uniform_bound` — ℓ²(embed f) ≤ q(f)² uniformly in Lt ≥ 1
- `torusGreen_uniform_bound` — **key result**: G_{Lt,Ls}(embed f, embed f) ≤ C · q(f)²
  uniformly in Lt ≥ 1

## Proof sketch (method of images)

The Green's function on the torus `T_{Lt,Ls}` is the periodization of the
cylinder Green's function:

  `G_{Lt,Ls}((x,t),(y,s)) = Σ_{k ∈ ℤ} G_{Ls}((x,t),(y,s + kLt))`

In the spectral representation, this is immediate: the Fourier modes on
`S¹_{Lt}` are the periodic subset of the full-line Fourier modes.

For test functions f supported on the cylinder (embedded into the torus by
periodization), the k=0 term gives the cylinder Green's function, and the
k≠0 terms are the "wrap-around" contributions from images.

Each image term involves the cylinder propagator evaluated at temporal
separation ≥ |k|Lt - diam(supp f). The mass gap gives exponential decay
`e^{-m|k|Lt}` (up to a polynomial prefactor absorbed into C(f)), so the
geometric series converges uniformly for Lt ≥ 1.

The Lean proof does not need the image decomposition: it uses the spectral bound
`G ≤ ℓ²/m²` (`greenFunctionBilinear_le`) together with the uniform ℓ² bound
`embed_l2_uniform_bound`, which rests on Bessel's inequality on `S¹_{Lt}` and the
unfolding `∫_0^{Lt} Σ_k |h(t + k Lt)| dt = ∫_ℝ |h|`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I, Ch. VIII
- Osterwalder-Schrader (1973), §3
-/
module

public import Cylinder.GreenFunction
public import Cylinder.Basic
public import Torus.AsymmetricTorus
public import Nuclear.GeneralMapCLM
public import SchwartzNuclear.Periodization
public import Mathlib.Algebra.Order.Interval.Set.Group

@[expose] public section

noncomputable section

namespace GaussianField

open NuclearTensorProduct

variable (Ls : ℝ) [hLs : Fact (0 < Ls)]

/-! ## Embedding cylinder test functions into the asymmetric torus

A test function `f ∈ CylinderTestFunction Ls = C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)` can be
embedded into the asymmetric torus `AsymTorusTestFunction Lt Ls` by
periodizing the Schwartz (temporal) factor: `𝓢(ℝ) → C∞(S¹_{Lt})`.

For Lt large relative to the effective support of f, this periodization
preserves essentially all the information in f. -/

/-- **Periodization embedding**: embeds cylinder test functions into the
asymmetric torus by periodizing the temporal (Schwartz) direction to
period Lt.

For `f = g ⊗ h ∈ C∞(S¹_{Ls}) ⊗̂ 𝓢(ℝ)`, the image is
`g ⊗ (periodize_{Lt} h) ∈ C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})`.

The periodization `periodize_{Lt} : 𝓢(ℝ) → C∞(S¹_{Lt})` sums the
translates: `(periodize_{Lt} h)(t) = Σ_{k ∈ ℤ} h(t + kLt)`. This sum
converges absolutely and uniformly (with all derivatives) because h is
Schwartz class. -/
def cylinderToTorusEmbed (Lt : ℝ) [Fact (0 < Lt)] :
    CylinderTestFunction Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  (nuclearTensorProduct_swapCLM
    (E₁ := SmoothMap_Circle Ls ℝ) (E₂ := SmoothMap_Circle Lt ℝ)).comp
  (nuclearTensorProduct_mapCLM_general
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ))
    (periodizeCLM Lt))

/-! ## Torus Green's function on the asymmetric torus

The continuum Green's function on the asymmetric torus `T_{Lt,Ls}` is
the spectral sum:

  `G_{Lt,Ls}(f, g) = Σ_{(n₁,n₂)} c_{n₁,n₂}(f) · c_{n₁,n₂}(g) / (μ_{n₁} + μ_{n₂} + m²)`

where `μ_{n₁}` are eigenvalues of `-Δ` on `S¹_{Lt}` and `μ_{n₂}` are
eigenvalues of `-Δ` on `S¹_{Ls}`.

This is the `greenFunctionBilinear` applied to `AsymTorusTestFunction Lt Ls`,
which already has `HasLaplacianEigenvalues` via the tensor product instance. -/

/-- The continuum Green's function on the asymmetric torus `T_{Lt,Ls}`.

This is `greenFunctionBilinear` applied to the tensor product of circle
spaces with periods Lt and Ls. The eigenvalues are sums
`(2πn₁/Lt)² + (2πn₂/Ls)²` from the tensor product instance. -/
def asymTorusContinuumGreen (Lt : ℝ) [Fact (0 < Lt)]
    (mass : ℝ) (hmass : 0 < mass)
    (f g : AsymTorusTestFunction Lt Ls) : ℝ :=
  greenFunctionBilinear mass hmass f g

/-! ## Cylinder Green's function: continuous seminorm bound

The cylinder Green's function `G_{Ls}(f, f)` is bounded by a continuous
seminorm of f. This follows from continuity of the mass operator
`T : CylinderTestFunction Ls → ℓ²` and the Cauchy-Schwarz inequality. -/

/-- **The cylinder Green's function is bounded by a continuous seminorm.**

There exists a continuous seminorm `q` on `CylinderTestFunction Ls` such that

  `G_{Ls}(f, f) ≤ q(f) ^ 2`

for all test functions f.

**Proof sketch**: Since `G_{Ls}(f, f) = ‖T f‖²_{ℓ²}` where
`T : CylinderTestFunction Ls →L[ℝ] ℓ²` is the continuous mass operator,
we have `G_{Ls}(f, f) = ‖T f‖² ≤ ‖T‖² · ‖f‖²`. More precisely, since
`CylinderTestFunction Ls` is a nuclear Fréchet space (not normed), the
continuity of T means there exists a continuous seminorm p with
`‖Tf‖ ≤ p(f)`, giving `G_{Ls}(f, f) ≤ p(f)²`. -/
theorem cylinderGreen_continuous_seminorm_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ f : CylinderTestFunction Ls,
        cylinderGreen Ls mass hmass f f ≤ q f ^ 2 := by
  -- The seminorm q(f) = ‖Tf‖ where T is the mass operator
  let T := cylinderMassOperator Ls mass hmass
  refine ⟨(normSeminorm ℝ ell2').comp T.toLinearMap, ?_, ?_⟩
  · -- Continuity: q = norm ∘ T, both continuous
    exact continuous_norm.comp T.cont
  · -- Bound: G(f,f) = ⟨Tf, Tf⟩ = ‖Tf‖² = q(f)²
    intro f
    simp only [cylinderGreen, Seminorm.comp_apply, coe_normSeminorm]
    exact le_of_eq (real_inner_self_eq_norm_sq (cylinderMassOperator Ls mass hmass f))

/-! ## Uniform ℓ² bound for embedded functions

The key estimate: the ℓ² norm of `embed f` (on the torus) is bounded
by a continuous seminorm of `f` (on the cylinder), uniformly in Lt ≥ 1.

This follows from the uniform boundedness of the periodization CLM:
`periodize_Lt(h)` has ℓ² norm bounded by a Schwartz seminorm of `h`,
uniformly in Lt ≥ 1 (`l2InnerProduct_periodizeCLM_le`). For `t ∈ [0, Lt]` the
periodization sum `Σ_k |h(t + kLt)|` is bounded by `4 S(h) Σ_k G(k)` with `G` summable and
independent of `Lt ≥ 1`, and its integral over `[0, Lt]` is `∫_ℝ |h|`; Bessel's inequality
then bounds the ℓ² norm by `∫_0^{Lt} |periodize_Lt h|²`. -/

/-- **ℓ² inner product factors for pure tensors.**

For pure tensors in an NTP: `‖pure(a,b)‖²_{ℓ²} = ‖a‖²_{ℓ²} · ‖b‖²_{ℓ²}`.
This follows from the coefficient factorization
`pure(a,b).val(pair(i,j)) = coeff_i(a) · coeff_j(b)`
and Fubini for absolutely convergent double sums. -/
theorem l2InnerProduct_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (a : E₁) (b : E₂) :
    l2InnerProduct (NuclearTensorProduct.pure a b) (NuclearTensorProduct.pure a b) =
    l2InnerProduct a a * l2InnerProduct b b := by
  -- Factor sequences
  set ca := fun i => DyninMityaginSpace.coeff i a
  set cb := fun j => DyninMityaginSpace.coeff j b
  set f₁ : ℕ → ℝ := fun i => ca i * ca i
  set f₂ : ℕ → ℝ := fun j => cb j * cb j
  -- Step 1: Show the LHS summand factors through Cantor pairing
  -- For NTP, coeff m f = f.val m (definitional), and
  -- (pure a b).val m = ca (unpair m).1 * cb (unpair m).2 (by pure_val)
  have h_term : ∀ m,
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure a b) *
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure a b) =
      f₁ (Nat.unpair m).1 * f₂ (Nat.unpair m).2 := by
    intro m
    show (NuclearTensorProduct.pure a b).val m *
      (NuclearTensorProduct.pure a b).val m =
      f₁ (Nat.unpair m).1 * f₂ (Nat.unpair m).2
    simp only [NuclearTensorProduct.pure_val, f₁, f₂]; ring
  -- Step 2: Rewrite l2InnerProduct as tsum and apply term factorization
  show ∑' m, DyninMityaginSpace.coeff m (NuclearTensorProduct.pure a b) *
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure a b) =
    (∑' i, ca i * ca i) * (∑' j, cb j * cb j)
  simp_rw [h_term]
  -- Step 3: Reindex from ℕ to ℕ × ℕ via Cantor pairing
  simp_rw [show Nat.unpair = ⇑Nat.pairEquiv.symm from Nat.pairEquiv_symm_apply.symm]
  rw [Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => f₁ p.1 * f₂ p.2)]
  -- Step 4: Factor the double sum using norm-summability
  have h1 : Summable (fun i => ‖f₁ i‖) :=
    (l2InnerProduct_summable a a).norm.congr (fun _ => rfl)
  have h2 : Summable (fun j => ‖f₂ j‖) :=
    (l2InnerProduct_summable b b).norm.congr (fun _ => rfl)
  exact (tsum_mul_tsum_of_summable_norm h1 h2).symm

/-- Local helper: swap Cantor pair components. -/
private def pairSwap' (m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair m).2 (Nat.unpair m).1

private theorem pairSwap'_involutive : Function.Involutive pairSwap' := fun m => by
  show Nat.pair (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).2
    (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).1 = m
  rw [Nat.unpair_pair]
  exact Nat.pair_unpair m

private def pairSwap'Equiv : ℕ ≃ ℕ :=
  pairSwap'_involutive.toPerm pairSwap'

@[simp] private theorem pairSwap'Equiv_apply (m : ℕ) :
    pairSwap'Equiv m = pairSwap' m :=
  congr_fun pairSwap'_involutive.coe_toPerm m

theorem l2InnerProduct_swap
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (f : NuclearTensorProduct E₁ E₂) :
    l2InnerProduct (nuclearTensorProduct_swapCLM f) (nuclearTensorProduct_swapCLM f) =
    l2InnerProduct f f := by
  -- l2InnerProduct g g = ∑' m, g.val m * g.val m (for NTP elements)
  -- (swapCLM f).val m = f.val (pairSwap' m) (definitional)
  -- So LHS = ∑' m, f.val(pairSwap' m)² = ∑' m, f.val(m)² = RHS
  -- by reindexing via the involutive bijection pairSwap'Equiv
  show ∑' m, (nuclearTensorProduct_swapCLM f).val m *
      (nuclearTensorProduct_swapCLM f).val m =
    ∑' m, f.val m * f.val m
  -- The swap is definitionally f.val(pairSwap' m)
  have h_eq : ∀ m, (nuclearTensorProduct_swapCLM f).val m = f.val (pairSwap' m) := by
    intro m; rfl
  simp_rw [h_eq]
  -- Reindex by the bijection pairSwap'Equiv
  rw [← pairSwap'Equiv.tsum_eq]
  simp only [pairSwap'Equiv_apply, pairSwap'_involutive _]

/-- **ℓ² inner product is bounded by a continuous seminorm squared.**

For any DyninMityaginSpace E: `l2InnerProduct f f ≤ C * q(f)²` where q is
a continuous seminorm. This follows from coeff_decay at exponent 2:
`|coeff m f|² ≤ C² * q(f)² / (1+m)⁴`, and `∑ 1/(1+m)⁴ < ∞`. -/
private theorem l2InnerProduct_le_seminorm
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ E),
      Continuous q ∧ ∀ f : E, l2InnerProduct f f ≤ C * q f ^ 2 := by
  -- Get coeff_decay at exponent 2
  obtain ⟨Cd, hCd, s, hbound⟩ := DyninMityaginSpace.coeff_decay (E := E) 2
  set q := s.sup DyninMityaginSpace.p
  have hq_cont : Continuous q := by
    apply Seminorm.continuous_of_le _ (Seminorm.finset_sup_le_sum _ _)
    show Continuous fun (x : E) =>
      (FunLike.coeAddMonoidHom (Seminorm ℝ E) E ℝ) (∑ i ∈ s, DyninMityaginSpace.p i) x
    simp_rw [map_sum, Finset.sum_apply]
    exact continuous_finsetSum _ fun i _ =>
      DyninMityaginSpace.h_with.continuous_seminorm i
  -- The bounding series ∑ 1/(1+m)^4 converges
  have h1_4 : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 4) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4))
    exact this.congr (fun m => by push_cast; ring_nf)
  set S := ∑' m : ℕ, (1 : ℝ) / ((m : ℝ) + 1) ^ 4
  have hS_pos : 0 < S := h1_4.tsum_pos (fun m => by positivity) 0 (by positivity)
  refine ⟨Cd ^ 2 * S, by positivity, q, hq_cont, fun f => ?_⟩
  -- Bound: l2(f,f) = ∑ (coeff m f)² ≤ ∑ (Cd * q f)² / (1+m)⁴
  show ∑' m, DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f ≤
    Cd ^ 2 * S * q f ^ 2
  have h_pw : ∀ m, DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f ≤
      Cd ^ 2 * q f ^ 2 * (1 / ((m : ℝ) + 1) ^ 4) := by
    intro m
    have hm_pos : (0 : ℝ) < 1 + (m : ℝ) := by positivity
    -- |coeff m f| * (1+m)^2 ≤ Cd * q f
    have h_abs : |DyninMityaginSpace.coeff m f| ≤ Cd * q f / (1 + (m : ℝ)) ^ 2 := by
      rw [le_div_iff₀ (pow_pos hm_pos 2)]
      exact hbound f m
    -- (coeff m f)^2 ≤ (Cd * q f / (1+m)^2)^2 = Cd² * q(f)² / (1+m)^4
    have h_sq : DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f =
        |DyninMityaginSpace.coeff m f| ^ 2 := by
      nlinarith [sq_nonneg (DyninMityaginSpace.coeff m f),
                 sq_abs (DyninMityaginSpace.coeff m f)]
    calc DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f
        = |DyninMityaginSpace.coeff m f| ^ 2 := h_sq
      _ ≤ (Cd * q f / (1 + (m : ℝ)) ^ 2) ^ 2 :=
          sq_le_sq' (by linarith [abs_nonneg (DyninMityaginSpace.coeff m f)]) h_abs
      _ = Cd ^ 2 * q f ^ 2 * (1 / ((m : ℝ) + 1) ^ 4) := by
          field_simp; ring
  calc ∑' m, DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m f
      ≤ ∑' (m : ℕ), Cd ^ 2 * q f ^ 2 * (1 / ((m : ℝ) + 1) ^ 4) :=
        (l2InnerProduct_summable f f).tsum_le_tsum h_pw (h1_4.mul_left _)
    _ = Cd ^ 2 * q f ^ 2 * S := tsum_mul_left
    _ = Cd ^ 2 * S * q f ^ 2 := by ring

/-! ### Analytic inputs for the uniform ℓ² bound -/

section UniformL2

open MeasureTheory

/-- `k ↦ (1 + |k|)⁻²` is summable over `ℤ`. -/
theorem summable_inv_one_add_abs_int_sq :
    Summable (fun k : ℤ => ((1 + |(k : ℝ)|) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    have := (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    refine this.congr fun n => ?_
    push_cast; rw [one_div, add_comm]
  refine summable_int_iff_summable_nat_and_neg.mpr ⟨?_, ?_⟩
  · refine hnat.congr fun n => ?_; simp
  · refine hnat.congr fun n => ?_; simp

/-- For `L ≥ 1` and `t ∈ [0, L]`, the shifted weight `(1 + |t + kL|)⁻²` is dominated by a
summable function of `k` that does not depend on `t` or `L`. -/
theorem inv_one_add_abs_shift_sq_le {L t : ℝ} (hL : 1 ≤ L) (ht : t ∈ Set.Icc 0 L) (k : ℤ) :
    ((1 + |t + k * L|) ^ 2)⁻¹ ≤
      ((1 + |(k : ℝ)|) ^ 2)⁻¹ + ((1 + |((k + 1 : ℤ) : ℝ)|) ^ 2)⁻¹ := by
  obtain ⟨ht0, htL⟩ := ht
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : |(k : ℝ)| ≤ |t + k * L| := by
      rw [abs_of_nonneg hk', abs_of_nonneg (by nlinarith)]
      nlinarith
    have : ((1 + |t + k * L|) ^ 2)⁻¹ ≤ ((1 + |(k : ℝ)|) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr)
    linarith [show (0 : ℝ) ≤ ((1 + |((k + 1 : ℤ) : ℝ)|) ^ 2)⁻¹ by positivity]
  · have hk' : (k : ℝ) + 1 ≤ 0 := by
      have : k + 1 ≤ 0 := hk
      exact_mod_cast this
    have h1 : |((k + 1 : ℤ) : ℝ)| ≤ |t + k * L| := by
      push_cast
      rw [abs_of_nonpos hk', abs_of_nonpos (by nlinarith)]
      nlinarith
    have : ((1 + |t + k * L|) ^ 2)⁻¹ ≤ ((1 + |((k + 1 : ℤ) : ℝ)|) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (by gcongr)
    linarith [show (0 : ℝ) ≤ ((1 + |(k : ℝ)|) ^ 2)⁻¹ by positivity]

/-- Pointwise decay of a Schwartz function from the seminorms with `(k, n) ≤ (2, 0)`. -/
theorem schwartz_abs_le_inv_one_add_sq (h : SchwartzMap ℝ ℝ) (x : ℝ) :
    |h x| ≤ 4 * (Finset.Iic (2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h *
      ((1 + |x|) ^ 2)⁻¹ := by
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2, 0)) (k := 2) (n := 0)
    le_rfl le_rfl h x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  norm_num at this ⊢
  linarith

/-- **Unfolding.** `∫_{[0,L]} Σ_k |h(t + kL)| dt = ∫_ℝ |h|`. -/
theorem integral_Icc_tsum_abs_shift (L : ℝ) (hL : 0 < L) (h : SchwartzMap ℝ ℝ) :
    ∫ t in Set.Icc 0 L, ∑' k : ℤ, |h (t + k * L)| = ∫ x, |h x| := by
  have hpiece : ∀ k : ℤ, ∫ t in Set.Icc 0 L, |h (t + k * L)| =
      ∫ x in Set.Ioc ((0 : ℝ) + k • L) (0 + (k + 1) • L), |h x| := by
    intro k
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
      intervalIntegral.integral_comp_add_right (fun x => |h x|),
      intervalIntegral.integral_of_le (by linarith)]
    congr 2
    simp only [zsmul_eq_mul, zero_add, Int.cast_add, Int.cast_one]
    congr 1; ring
  have hsum : HasSum (fun k : ℤ => ∫ x in Set.Ioc ((0 : ℝ) + k • L) (0 + (k + 1) • L), |h x|)
      (∫ x, |h x|) := by
    have := hasSum_integral_iUnion (μ := volume) (f := fun x => |h x|)
      (fun k : ℤ => measurableSet_Ioc) (Set.pairwise_disjoint_Ioc_add_zsmul (0 : ℝ) L)
      (h.integrable.abs.integrableOn)
    rwa [iUnion_Ioc_add_zsmul hL, setIntegral_univ] at this
  have hint : ∀ k : ℤ,
      Integrable (fun t => |h (t + k * L)|) (volume.restrict (Set.Icc 0 L)) := fun k =>
    (continuous_abs.comp (h.continuous.comp (continuous_id.add continuous_const))).integrableOn_Icc
  rw [← integral_tsum_of_summable_integral_norm hint]
  · simp_rw [hpiece]; exact hsum.tsum_eq
  · simp_rw [Real.norm_eq_abs, abs_abs, hpiece]; exact hsum.summable

/-- `∫_ℝ |h| ≤ 4 I · S(h)` with `I = ∫ (1 + |x|)⁻²` and `S` the `(2, 0)`-seminorm sup. -/
theorem integral_abs_schwartz_le (h : SchwartzMap ℝ ℝ) :
    ∫ x, |h x| ≤ 4 * (Finset.Iic (2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h *
      ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹ := by
  have hI : Integrable (fun x : ℝ => ((1 + |x|) ^ 2)⁻¹) := by
    have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs]
    rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rw [← integral_const_mul]
  exact integral_mono h.integrable.abs (hI.const_mul _) fun x => schwartz_abs_le_inv_one_add_sq h x

/-- **Bessel's inequality** for the real Fourier basis of `C∞(S¹_L)`:
`Σ_n c_n(g)² ≤ ∫_{[0,L]} g²`. -/
theorem l2InnerProduct_smoothCircle_le (L : ℝ) [Fact (0 < L)] (g : SmoothMap_Circle L ℝ) :
    l2InnerProduct g g ≤ ∫ x in Set.Icc 0 L, g x ^ 2 := by
  set ψ : ℕ → ℝ → ℝ := fun n => SmoothMap_Circle.fourierBasisFun (L := L) n
  set c : ℕ → ℝ := fun n => SmoothMap_Circle.fourierCoeffReal (L := L) n g
  have hψc : ∀ n, Continuous (ψ n) := fun n =>
    (SmoothMap_Circle.fourierBasisFun_smooth n).continuous
  have hint : ∀ f : ℝ → ℝ, Continuous f → Integrable f (volume.restrict (Set.Icc 0 L)) :=
    fun f hf => hf.integrableOn_Icc
  have horth : ∀ i j, ∫ x in Set.Icc 0 L, ψ j x * ψ i x = if i = j then 1 else 0 := by
    intro i j
    have := SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := L) i j
    simpa [SmoothMap_Circle.fourierCoeffReal, SmoothMap_Circle.fourierBasis_apply] using this
  have hc : ∀ n, ∫ x in Set.Icc 0 L, g x * ψ n x = c n := fun n => rfl
  have hgψ : ∀ n, Continuous (fun x => g x * ψ n x) := fun n => g.continuous.mul (hψc n)
  have hψψ : ∀ n m, Continuous (fun x => ψ m x * ψ n x) := fun n m => (hψc m).mul (hψc n)
  have hfin : ∀ s : Finset ℕ, ∑ n ∈ s, c n * c n ≤ ∫ x in Set.Icc 0 L, g x ^ 2 := by
    intro s
    have h0 : 0 ≤ ∫ x in Set.Icc 0 L, (g x - ∑ n ∈ s, c n * ψ n x) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have e : ∀ x, (g x - ∑ n ∈ s, c n * ψ n x) ^ 2 = g x ^ 2 -
        2 * ∑ n ∈ s, c n * (g x * ψ n x) +
        ∑ n ∈ s, ∑ m ∈ s, c n * c m * (ψ m x * ψ n x) := by
      intro x
      have h1 : (∑ n ∈ s, c n * ψ n x) ^ 2 =
          ∑ n ∈ s, ∑ m ∈ s, c n * c m * (ψ m x * ψ n x) := by
        rw [sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => by ring
      have h2 : 2 * g x * ∑ n ∈ s, c n * ψ n x = 2 * ∑ n ∈ s, c n * (g x * ψ n x) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by ring
      rw [sub_sq, h1, h2]
    have hS₁ : Continuous (fun x => 2 * ∑ n ∈ s, c n * (g x * ψ n x)) :=
      continuous_const.mul (continuous_finsetSum _ fun n _ => continuous_const.mul (hgψ n))
    have hS₂ : Continuous (fun x => ∑ n ∈ s, ∑ m ∈ s, c n * c m * (ψ m x * ψ n x)) :=
      continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun m _ =>
        continuous_const.mul (hψψ n m)
    have hg2 : Continuous (fun x => g x ^ 2) := g.continuous.pow 2
    have hB : ∫ x in Set.Icc 0 L, 2 * ∑ n ∈ s, c n * (g x * ψ n x) =
        2 * ∑ n ∈ s, c n * c n := by
      rw [integral_const_mul,
        integral_finsetSum _ fun n _ =>
          hint (fun x => c n * (g x * ψ n x)) (continuous_const.mul (hgψ n))]
      congr 1
      exact Finset.sum_congr rfl fun n _ => by rw [integral_const_mul, hc]
    have hC : ∫ x in Set.Icc 0 L, ∑ n ∈ s, ∑ m ∈ s, c n * c m * (ψ m x * ψ n x) =
        ∑ n ∈ s, c n * c n := by
      rw [integral_finsetSum _ fun n _ =>
        hint (fun x => ∑ m ∈ s, c n * c m * (ψ m x * ψ n x))
          (continuous_finsetSum _ fun m _ => continuous_const.mul (hψψ n m))]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [integral_finsetSum _ fun m _ =>
        hint (fun x => c n * c m * (ψ m x * ψ n x)) (continuous_const.mul (hψψ n m))]
      simp_rw [integral_const_mul, horth, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]; simp [hn]
    have hval : ∫ x in Set.Icc 0 L, (g x - ∑ n ∈ s, c n * ψ n x) ^ 2 =
        (∫ x in Set.Icc 0 L, g x ^ 2) - ∑ n ∈ s, c n * c n := by
      simp_rw [e]
      rw [integral_add (f := fun x => g x ^ 2 - 2 * ∑ n ∈ s, c n * (g x * ψ n x))
        ((hint _ hg2).sub (hint _ hS₁)) (hint _ hS₂), integral_sub (hint _ hg2) (hint _ hS₁),
        hB, hC]
      ring
    linarith
  exact Real.tsum_le_of_sum_le (fun n => mul_self_nonneg _) hfin

/-- **Uniform ℓ² bound for periodization.** There is `C` such that for every period `L ≥ 1`
and every Schwartz `h`, the Fourier-coefficient ℓ² norm of the periodization satisfies
`Σ_n c_n(P_L h)² ≤ C · S(h)²`, with `S` the sup of the Schwartz seminorms `p_{a,0}`, `a ≤ 2`. -/
theorem l2InnerProduct_periodizeCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) [Fact (0 < L)], 1 ≤ L → ∀ h : SchwartzMap ℝ ℝ,
      l2InnerProduct (periodizeCLM L h) (periodizeCLM L h) ≤
        C * ((Finset.Iic (2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h) ^ 2 := by
  set G : ℤ → ℝ := fun k => ((1 + |(k : ℝ)|) ^ 2)⁻¹ + ((1 + |((k + 1 : ℤ) : ℝ)|) ^ 2)⁻¹
  have hG : Summable G := summable_inv_one_add_abs_int_sq.add
    (summable_inv_one_add_abs_int_sq.comp_injective (add_left_injective 1))
  set c₁ := ∑' k, G k
  set I := ∫ x : ℝ, ((1 + |x|) ^ 2)⁻¹
  have hc₁ : 0 ≤ c₁ := tsum_nonneg fun k => by positivity
  have hI : 0 ≤ I := integral_nonneg fun x => by positivity
  refine ⟨16 * c₁ * I, by positivity, fun L _ hL h => ?_⟩
  set S := (Finset.Iic (2, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h
  have hS : 0 ≤ S := apply_nonneg _ _
  have hL0 : 0 < L := by linarith
  have hdom : ∀ t ∈ Set.Icc 0 L, ∀ k : ℤ, ‖|h (t + k * L)|‖ ≤ 4 * S * G k := by
    intro t ht k
    rw [Real.norm_eq_abs, abs_abs]
    calc |h (t + k * L)| ≤ 4 * S * ((1 + |t + k * L|) ^ 2)⁻¹ :=
          schwartz_abs_le_inv_one_add_sq h _
      _ ≤ 4 * S * G k := by gcongr; exact inv_one_add_abs_shift_sq_le hL ht k
  have hsum_t : ∀ t ∈ Set.Icc 0 L, Summable (fun k : ℤ => |h (t + k * L)|) := fun t ht =>
    (hG.mul_left (4 * S)).of_norm_bounded (hdom t ht)
  set F : ℝ → ℝ := fun t => ∑' k : ℤ, |h (t + k * L)|
  have hF_nonneg : ∀ t, 0 ≤ F t := fun t => tsum_nonneg fun k => abs_nonneg _
  have hF_le : ∀ t ∈ Set.Icc 0 L, F t ≤ 4 * S * c₁ := fun t ht => by
    calc F t ≤ ∑' k, 4 * S * G k :=
          (hsum_t t ht).tsum_le_tsum (fun k => by simpa using hdom t ht k) (hG.mul_left _)
      _ = 4 * S * c₁ := tsum_mul_left
  have hP_le : ∀ t ∈ Set.Icc 0 L, |periodizeCLM L h t| ≤ F t := fun t ht => by
    have hsum : Summable (fun k : ℤ => ‖h (t + k * L)‖) := by
      simpa [Real.norm_eq_abs] using hsum_t t ht
    calc |periodizeCLM L h t| = ‖∑' k : ℤ, h (t + k * L)‖ := rfl
      _ ≤ ∑' k : ℤ, ‖h (t + k * L)‖ := norm_tsum_le_tsum_norm hsum
      _ = F t := by simp [F, Real.norm_eq_abs]
  have hFcont : ContinuousOn F (Set.Icc 0 L) :=
    continuousOn_tsum (fun k => (continuous_abs.comp (h.continuous.comp
      (continuous_id.add continuous_const))).continuousOn) (hG.mul_left (4 * S))
      (fun k t ht => hdom t ht k)
  have hFint : IntegrableOn F (Set.Icc 0 L) := hFcont.integrableOn_Icc
  have hPc : Continuous (fun t => periodizeCLM L h t ^ 2) := (periodizeCLM L h).continuous.pow 2
  calc l2InnerProduct (periodizeCLM L h) (periodizeCLM L h)
      ≤ ∫ t in Set.Icc 0 L, periodizeCLM L h t ^ 2 := l2InnerProduct_smoothCircle_le L _
    _ ≤ ∫ t in Set.Icc 0 L, 4 * S * c₁ * F t := by
        refine setIntegral_mono_on hPc.integrableOn_Icc (hFint.const_mul _) measurableSet_Icc
          fun t ht => ?_
        rw [← sq_abs]
        calc |periodizeCLM L h t| ^ 2 ≤ F t ^ 2 :=
              pow_le_pow_left₀ (abs_nonneg _) (hP_le t ht) 2
          _ = F t * F t := sq _
          _ ≤ 4 * S * c₁ * F t := mul_le_mul_of_nonneg_right (hF_le t ht) (hF_nonneg t)
    _ = 4 * S * c₁ * ∫ x, |h x| := by
        rw [integral_const_mul, integral_Icc_tsum_abs_shift L hL0 h]
    _ ≤ 4 * S * c₁ * (4 * S * I) := by
        gcongr
        exact integral_abs_schwartz_le h
    _ = 16 * c₁ * I * S ^ 2 := by ring

/-- **ℓ² Minkowski inequality** for a coefficientwise series:
`‖Σ_m x_m v_m‖_{ℓ²}² ≤ (Σ_m |x_m| ‖v_m‖_{ℓ²})²`. -/
theorem tsum_sq_tsum_mul_le (x : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (hv : ∀ m, Summable (fun n => v m n ^ 2))
    (hx : Summable (fun m => |x m| * Real.sqrt (∑' n, v m n ^ 2))) :
    ∑' n, (∑' m, x m * v m n) ^ 2 ≤ (∑' m, |x m| * Real.sqrt (∑' n, v m n ^ 2)) ^ 2 := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  have hnorm : ∀ W : lp (fun _ : ℕ => ℝ) 2, ‖W‖ = Real.sqrt (∑' n, W n ^ 2) := by
    intro W
    rw [lp.norm_eq_tsum_rpow hp, Real.sqrt_eq_rpow]
    simp [Real.norm_eq_abs, sq_abs]
  let V : ℕ → lp (fun _ : ℕ => ℝ) 2 := fun m =>
    ⟨v m, memℓp_gen (by simpa [Real.norm_eq_abs, sq_abs] using hv m)⟩
  have hVn : ∀ m, ‖V m‖ = Real.sqrt (∑' n, v m n ^ 2) := fun m => hnorm (V m)
  have hnsum : Summable (fun m => ‖x m • V m‖) := by
    simpa [norm_smul, hVn, Real.norm_eq_abs] using hx
  have hsumm : Summable (fun m => x m • V m) := hnsum.of_norm
  set W := ∑' m, x m • V m
  have hW : ∀ n, W n = ∑' m, x m * v m n := by
    intro n
    have := (hsumm.hasSum.mapL (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n)).tsum_eq
    exact this.symm
  have hWle : ‖W‖ ≤ ∑' m, |x m| * Real.sqrt (∑' n, v m n ^ 2) := by
    calc ‖W‖ ≤ ∑' m, ‖x m • V m‖ := norm_tsum_le_tsum_norm hnsum
      _ = _ := by simp [norm_smul, hVn, Real.norm_eq_abs]
  calc ∑' n, (∑' m, x m * v m n) ^ 2 = ∑' n, W n ^ 2 := by simp_rw [hW]
    _ = ‖W‖ ^ 2 := by rw [hnorm W, Real.sq_sqrt (tsum_nonneg fun n => sq_nonneg _)]
    _ ≤ _ := pow_le_pow_left₀ (norm_nonneg _) hWle 2

/-- A basis vector of a biorthogonal Dynin–Mityagin space has unit ℓ² coefficient norm. -/
theorem l2InnerProduct_basis_self
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E]
    [DyninMityaginSpace.HasBiorthogonalBasis E] (a : ℕ) :
    l2InnerProduct (DyninMityaginSpace.basis (E := E) a) (DyninMityaginSpace.basis a) = 1 := by
  show ∑' n, DyninMityaginSpace.coeff n (DyninMityaginSpace.basis (E := E) a) *
    DyninMityaginSpace.coeff n (DyninMityaginSpace.basis (E := E) a) = 1
  simp only [DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis, mul_ite, mul_one, mul_zero]
  simp

/-- Polynomial growth of the Schwartz seminorms `p_{a,0}`, `a ≤ 2`, on the Hermite basis. -/
theorem schwartz_basis_sup_seminorm_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ S : ℕ, ∀ b : ℕ,
      (Finset.Iic (2, 0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
        (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b) ≤ K * (1 + (b : ℝ)) ^ S := by
  classical
  have hcont : Continuous ((Finset.Iic (2, 0)).sup
      (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) : Seminorm ℝ (SchwartzMap ℝ ℝ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm i
  obtain ⟨t, C', -, hle⟩ := Seminorm.bound_of_continuous
    (DyninMityaginSpace.h_with (E := SchwartzMap ℝ ℝ)) _ hcont
  obtain ⟨K, hK, S, hbnd⟩ := finset_sup_poly_bound DyninMityaginSpace.p t
    (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ))
    (fun i _ => DyninMityaginSpace.basis_growth i)
  refine ⟨C' * K, by positivity, S, fun b => ?_⟩
  calc _ ≤ (C' • t.sup DyninMityaginSpace.p)
        (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b) := hle _
    _ = C' * t.sup DyninMityaginSpace.p (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b) :=
        rfl
    _ ≤ C' * (K * (1 + (b : ℝ)) ^ S) := by gcongr; exact hbnd b
    _ = C' * K * (1 + (b : ℝ)) ^ S := by ring

end UniformL2

/-- **Uniform ℓ² bound for the periodization embedding.**

The ℓ² coefficient norm of the embedded cylinder test function on the
torus is bounded by a continuous seminorm of f on the cylinder,
uniformly in Lt ≥ 1. This is the core tightness input.

**Proof.** `embed = swap ∘ (id ⊗ P_Lt)`, and `swap` preserves the ℓ² norm
(`l2InnerProduct_swap`). The coefficients of `(id ⊗ P_Lt) f` are
`Σ_m f_m · v_m` with `v_m = pure (ψ_a) (P_Lt h_b)`, `(a, b) = unpair m`, so by the ℓ²
Minkowski inequality (`tsum_sq_tsum_mul_le`)
  `l2(embed f) ≤ (Σ_m |f_m| · ‖v_m‖_{ℓ²})²`,
and `‖v_m‖²_{ℓ²} = l2(ψ_a) · l2(P_Lt h_b) = l2(P_Lt h_b)` (`l2InnerProduct_pure`,
`l2InnerProduct_basis_self`). The periodization bound `l2InnerProduct_periodizeCLM_le`
(Bessel + unfolding, uniform in `Lt ≥ 1`) and polynomial growth of the Hermite basis
(`schwartz_basis_sup_seminorm_le`) give `‖v_m‖_{ℓ²} ≤ A (1 + m)^s`, hence
`l2(embed f) ≤ (A · rapidDecaySeminorm s f)²`.

Reference: Stein-Weiss, Ch. VII (periodization of rapidly decaying functions). -/
theorem embed_l2_uniform_bound :
    ∃ (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f : CylinderTestFunction Ls,
          l2InnerProduct
            (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
          q f ^ 2 := by
  obtain ⟨C, hC, hP⟩ := l2InnerProduct_periodizeCLM_le
  obtain ⟨K, hK, s, hbasis⟩ := schwartz_basis_sup_seminorm_le
  set A : ℝ := Real.sqrt C * K
  have hA : 0 ≤ A := by positivity
  refine ⟨A.toNNReal • RapidDecaySeq.rapidDecaySeminorm s, ?_, fun Lt _ hLt f => ?_⟩
  · exact (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm s).const_smul _
  set T₁ := ContinuousLinearMap.id ℝ (SmoothMap_Circle Ls ℝ)
  set G := nuclearTensorProduct_mapCLM_general T₁ (periodizeCLM Lt) f
  set v : ℕ → ℕ → ℝ := fun m n => (mapImageGen T₁ (periodizeCLM Lt) m).val n
  have hG : l2InnerProduct G G = ∑' n, (∑' m, f.val m * v m n) ^ 2 := by
    show ∑' n, G.val n * G.val n = _
    simp_rw [← sq]
    rfl
  have hv_eq : ∀ m, ∑' n, v m n ^ 2 =
      l2InnerProduct (periodizeCLM Lt (DyninMityaginSpace.basis (Nat.unpair m).2))
        (periodizeCLM Lt (DyninMityaginSpace.basis (Nat.unpair m).2)) := by
    intro m
    have h := l2InnerProduct_pure
      (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).1)
      (periodizeCLM Lt (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair m).2))
    rw [l2InnerProduct_basis_self, one_mul] at h
    rw [← h]
    show ∑' n, v m n ^ 2 = ∑' n, (mapImageGen T₁ (periodizeCLM Lt) m).val n *
      (mapImageGen T₁ (periodizeCLM Lt) m).val n
    simp_rw [sq]
    rfl
  have hv : ∀ m, Summable (fun n => v m n ^ 2) := fun m => by
    have := l2InnerProduct_summable (mapImageGen T₁ (periodizeCLM Lt) m)
      (mapImageGen T₁ (periodizeCLM Lt) m)
    refine this.congr fun n => ?_
    show (mapImageGen T₁ (periodizeCLM Lt) m).val n * (mapImageGen T₁ (periodizeCLM Lt) m).val n =
      v m n ^ 2
    rw [sq]
  have hsqrt : ∀ m, Real.sqrt (∑' n, v m n ^ 2) ≤ A * (1 + (m : ℝ)) ^ s := by
    intro m
    set b := (Nat.unpair m).2
    set S := (Finset.Iic (2, 0)).sup (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2)
      (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) b)
    have hS : 0 ≤ S := apply_nonneg _ _
    have hb : (1 + (b : ℝ)) ^ s ≤ (1 + (m : ℝ)) ^ s := by
      gcongr; exact_mod_cast Nat.unpair_right_le m
    rw [hv_eq]
    calc Real.sqrt _ ≤ Real.sqrt (C * S ^ 2) := Real.sqrt_le_sqrt (hP Lt hLt _)
      _ = Real.sqrt C * S := by rw [Real.sqrt_mul hC, Real.sqrt_sq hS]
      _ ≤ Real.sqrt C * (K * (1 + (b : ℝ)) ^ s) := by gcongr; exact hbasis b
      _ ≤ Real.sqrt C * (K * (1 + (m : ℝ)) ^ s) := by gcongr
      _ = A * (1 + (m : ℝ)) ^ s := by ring
  have hdom : ∀ m, |f.val m| * Real.sqrt (∑' n, v m n ^ 2) ≤
      A * (|f.val m| * (1 + (m : ℝ)) ^ s) := fun m => by
    calc |f.val m| * Real.sqrt (∑' n, v m n ^ 2) ≤ |f.val m| * (A * (1 + (m : ℝ)) ^ s) :=
          mul_le_mul_of_nonneg_left (hsqrt m) (abs_nonneg _)
      _ = A * (|f.val m| * (1 + (m : ℝ)) ^ s) := by ring
  have hx : Summable (fun m => |f.val m| * Real.sqrt (∑' n, v m n ^ 2)) :=
    Summable.of_nonneg_of_le (fun m => by positivity) hdom ((f.rapid_decay s).mul_left A)
  suffices key : l2InnerProduct (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
      (A * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ s) ^ 2 by
    refine key.trans (le_of_eq ?_)
    congr 1
    change A * _ = (A.toNNReal : ℝ) * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ s
    rw [Real.coe_toNNReal A hA]
  rw [show cylinderToTorusEmbed Ls Lt f = nuclearTensorProduct_swapCLM G from rfl,
    l2InnerProduct_swap, hG]
  calc ∑' n, (∑' m, f.val m * v m n) ^ 2
      ≤ (∑' m, |f.val m| * Real.sqrt (∑' n, v m n ^ 2)) ^ 2 :=
        tsum_sq_tsum_mul_le _ _ hv hx
    _ ≤ (∑' m, A * (|f.val m| * (1 + (m : ℝ)) ^ s)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun m => by positivity)
          (hx.tsum_le_tsum hdom ((f.rapid_decay s).mul_left A)) 2
    _ = (A * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ s) ^ 2 := by rw [tsum_mul_left]

/-! ## Uniform bound: the main result for Route B' IR limit -/

/-- **Uniform bound on the torus Green's function (Route B' IR limit).**

There exists a continuous seminorm `q` on `CylinderTestFunction Ls` and
a constant `C > 0` such that

  `G_{Lt,Ls}(embed f, embed f) ≤ C · q(f) ^ 2`

for all `f : CylinderTestFunction Ls` and all `Lt ≥ 1`.

**Proof**: From `greenFunctionBilinear_le` (G ≤ ℓ²/m²) and
`embed_l2_uniform_bound` (ℓ² of embed ≤ q²). -/
theorem torusGreen_uniform_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (C : ℝ) (_ : 0 < C) (q : Seminorm ℝ (CylinderTestFunction Ls)),
      Continuous q ∧
      ∀ (Lt : ℝ) [Fact (0 < Lt)],
        1 ≤ Lt →
        ∀ f : CylinderTestFunction Ls,
          asymTorusContinuumGreen Ls Lt mass hmass
            (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) ≤
          C * q f ^ 2 := by
  obtain ⟨q, hq_cont, hq_bound⟩ := embed_l2_uniform_bound Ls
  refine ⟨1 / mass ^ 2, by positivity, q, hq_cont, ?_⟩
  intro Lt _ hLt f
  -- G_torus(embed f, embed f) ≤ (1/m²) · l2(embed f, embed f)
  calc asymTorusContinuumGreen Ls Lt mass hmass
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f)
      = greenFunctionBilinear mass hmass
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) := rfl
    _ ≤ (1 / mass ^ 2) * l2InnerProduct
        (cylinderToTorusEmbed Ls Lt f) (cylinderToTorusEmbed Ls Lt f) :=
      greenFunctionBilinear_le mass hmass _
    _ ≤ (1 / mass ^ 2) * q f ^ 2 := by
      gcongr; exact hq_bound Lt hLt f

end GaussianField
