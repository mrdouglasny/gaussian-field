/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Mass-operator equivariance: discharge of `_norm_eq` instance axioms

The structure `CylinderSpacetimeSymmetry` (in `Cylinder/GreenFunction.lean`)
records that a CLM `S : CylinderTestFunction L → CylinderTestFunction L`
commutes with the heat semigroup *and* preserves the ℓ²-norm of the mass
operator output. The `preserves_T_norm` field is what was missing in the
earlier (false) `cylinderMassOperator_equivariant_of_heat_comm` axiom.

This file proves the `preserves_T_norm` field for two of the three concrete
Euclidean operators on the cylinder via a single parametric lemma.

## Main results

* `ntpSliceSchwartz_tensorMap_id_left` — slicing commutes with a tensor
  map that acts only on the temporal factor.
* `cylinderMassOperator_norm_eq_of_temporal_action` — parametric
  preservation of the mass-operator ℓ²-norm by a temporal-only action
  satisfying multiplier-commutativity and L²-isometry hypotheses.
* `cylinderMassOperator_timeReflection_norm_eq_proved` — concrete
  discharge for time reflection via the parametric lemma.
-/

import Cylinder.MassOperatorConstruction
import Cylinder.FourierMultiplier
import SchwartzNuclear.HermiteHilbertBasis
import Nuclear.NuclearExtension
import HeatKernel.GreenInvariance

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Step 1: Slice commutes with tensor map `id ⊗ S₂`

For any CLM `S₂ : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ`, slicing the
tensor-mapped function recovers `S₂` applied to the slice:

  `slice_a ((id ⊗ S₂) f) = S₂ (slice_a f)`.

Adapted from `future/CylinderReflectionPositivity.lean:666` (the
specialisation `S₂ = schwartzReflection`). The proof generalises
verbatim because it only uses `nuclearTensorProduct_mapCLM_pure` and
`ntpSliceSchwartz_pure`, neither of which fixes `S₂`. -/

private theorem ntpSliceSchwartz_tensorMap_id_left
    (S₂ : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ) (a : ℕ)
    (f : CylinderTestFunction L) :
    ntpSliceSchwartz L a
        (nuclearTensorProduct_mapCLM
          (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂ f) =
      S₂ (ntpSliceSchwartz L a f) := by
  -- Two CLMs agree iff they agree on the DM basis (Schauder + HasSum uniqueness).
  set T₁ : CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ :=
    (ntpSliceSchwartz L a).comp
      (nuclearTensorProduct_mapCLM
        (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂)
  set T₂ : CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ :=
    S₂.comp (ntpSliceSchwartz L a)
  change T₁ f = T₂ f
  suffices h : T₁ = T₂ from congr_fun (congr_arg _ h) f
  apply ContinuousLinearMap.ext; intro g
  have hg := DyninMityaginSpace.hasSum_basis g
  have h_basis : ∀ m, T₁ (DyninMityaginSpace.basis m) =
      T₂ (DyninMityaginSpace.basis m) := by
    intro m
    simp only [T₁, T₂, ContinuousLinearMap.comp_apply]
    -- NTP basis = pure of component bases
    rw [show (DyninMityaginSpace.basis (E := CylinderTestFunction L) m :
        CylinderTestFunction L) = NuclearTensorProduct.pure
        (DyninMityaginSpace.basis (Nat.unpair m).1)
        (DyninMityaginSpace.basis (Nat.unpair m).2) from
      NuclearTensorProduct.basisVec_eq_pure (GaussianField.smoothCircle_coeff_basis L)
        DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis m]
    -- (id ⊗ S₂)(pure g h) = pure g (S₂ h)
    rw [nuclearTensorProduct_mapCLM_pure, ntpSliceSchwartz_pure,
        ntpSliceSchwartz_pure, map_smul]
    simp [ContinuousLinearMap.id_apply]
  -- HasSum uniqueness: both sums have the same terms (by h_basis), hence same limit.
  have h1 := hg.mapL T₁
  have h2 := hg.mapL T₂
  simp only [map_smul] at h1 h2
  simp_rw [h_basis] at h1
  exact h1.unique h2

/-! ## Step 2: Schwartz reflection is L²-isometric

`∫ (Θ g)(t)² dt = ∫ g(t)² dt`, by change of variables `t ↦ -t`. -/

private theorem schwartzReflection_integral_sq (g : SchwartzMap ℝ ℝ) :
    ∫ t, (schwartzReflection g) t ^ 2 = ∫ t, g t ^ 2 := by
  -- schwartzReflection g t = g (-t) (definitionally; see Cylinder/Symmetry.lean:74).
  have h_eq : (fun t : ℝ => (schwartzReflection g) t ^ 2) =
      (fun t : ℝ => g (-t) ^ 2) := by
    funext t; rfl
  rw [h_eq]
  exact MeasureTheory.integral_neg_eq_self (G := ℝ) (fun t => g t ^ 2) MeasureTheory.volume

/-! ## Step 3: Mass-operator squared-norm via DM Parseval

For each spatial mode `a` and `f : CylinderTestFunction L`, define

  `S(a, f) := ‖resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
              (ntpSliceSchwartz L a f)‖²_{L²} = ∫ (R_{ω_a}(slice_a f))² dt`

via diagonal DM-Parseval. Then

  `‖cylinderMassOperator L mass hmass f‖²_{ell2'} = ∑' a, S(a, f)`

via the lp-2 norm formula plus Cantor reindexing.

This identity is the workhorse: norm preservation of the mass operator
under any operator `S` reduces to per-spatial-mode invariance of
`‖R_{ω_a}(slice_a (S f))‖²_{L²}`. -/

private def perModeL2SqNorm (mass : ℝ) (hmass : 0 < mass)
    (a : ℕ) (f : CylinderTestFunction L) : ℝ :=
  ∫ t, (resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
        (ntpSliceSchwartz L a f)) t ^ 2

/-- The mass operator's ℓ²-norm² decomposes as a per-spatial-mode L²-norm² sum.

    `‖T f‖²_{ell2'} = ∑' a, ∫ (R_{ω_a}(slice_a f))² dt`.

**Proof outline** (deferred — see line 142 sorry):

* **Step A**: `‖x‖²_{lp 2} = ⟪x, x⟫ = ∑' n, ⟪x.val n, x.val n⟫_ℝ`
  via `inner_self_eq_norm_sq_to_K` + `lp.inner_eq_tsum`.
* **Step B**: real inner product reduces to product:
  `⟪a, a⟫_ℝ = a * a = a^2`.
* **Step C**: substitute `cylinderMassOperator_formula`:
  `(T f).val n = DM_b(R_{ω_a}(slice_a f))` where `(a, b) = Nat.unpair n`.
* **Step D**: Cantor reindex via `Equiv.tsum_eq Nat.pairEquiv.symm`:
  `∑' n, F(Nat.unpair n) = ∑' (a,b), F(a,b)` then unfold to
  `∑' a, ∑' b, F(a,b)` (Tonelli for real-nonneg sums via
  `Summable.tsum_prod`).
* **Step E**: diagonal DM Parseval per spatial mode `a`:
  `∑' b, DM_b(R_{ω_a}(slice_a f))² = ∫ (R_{ω_a}(slice_a f))²`,
  obtained by setting `g = h = R_{ω_a}(slice_a f)` in
  `SchwartzNuclear.HermiteHilbertBasis.dm_parseval`.

Existing analogues: a similar Cantor-reindex pattern is used in
`future/CylinderReflectionPositivity.lean` line 750+ for
`cylinderGreen_reflection_eq_laplaceNorm`. The diagonal specialisation
here is simpler (single function instead of a pair). -/
private theorem cylinderMassOperator_normSq_eq_sum_perMode
    (mass : ℝ) (hmass : 0 < mass) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass f‖ ^ 2 =
    ∑' a, perModeL2SqNorm L mass hmass a f := by
  set Tf := cylinderMassOperator L mass hmass f with hTf_def
  -- Step A: ‖Tf‖² = ⟪Tf, Tf⟫_ℝ (real Hilbert space identity)
  rw [show ‖Tf‖ ^ 2 = @inner ℝ ell2' _ Tf Tf from
    (real_inner_self_eq_norm_sq Tf).symm]
  -- Step B: lp 2 inner = tsum of fiber inners
  rw [lp.inner_eq_tsum]
  -- Step C: real-fiber inner ⟪a, a⟫_ℝ = a * a = a^2
  simp_rw [show ∀ a : ℝ, @inner ℝ ℝ _ a a = a ^ 2 from
    fun a => by simp [inner, RCLike.re, conj_trivial, sq]]
  -- Step D: substitute cylinderMassOperator_formula
  simp_rw [show ∀ n, Tf n = (Tf : ℕ → ℝ) n from fun n => rfl,
           cylinderMassOperator_formula]
  -- Step E: Cantor reindex `∑' n, F (Nat.unpair n) = ∑' (p : ℕ × ℕ), F p`
  --   Using F (a, b) := (DM_b (R_{ω_a}(slice_a f)))^2
  set F : ℕ × ℕ → ℝ := fun p =>
    (DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) p.2
      (resolventMultiplierCLM (resolventFreq_pos L mass hmass p.1)
        (ntpSliceSchwartz L p.1 f))) ^ 2
  -- Note that the post-substitution sum has F applied to (Nat.unpair n) — we want
  -- to recognise that as ∑' p : ℕ × ℕ, F p.
  have hreindex : (∑' n : ℕ,
      (DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2
        (resolventMultiplierCLM (resolventFreq_pos L mass hmass (Nat.unpair n).1)
          (ntpSliceSchwartz L (Nat.unpair n).1 f))) ^ 2) =
      ∑' p : ℕ × ℕ, F p := by
    have hF_unpair : (fun n : ℕ => F (Nat.pairEquiv.symm n)) =
        (fun n : ℕ =>
          (DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2
            (resolventMultiplierCLM (resolventFreq_pos L mass hmass (Nat.unpair n).1)
              (ntpSliceSchwartz L (Nat.unpair n).1 f))) ^ 2) := by
      funext n
      simp [F, Nat.pairEquiv]
    rw [← hF_unpair]
    exact Equiv.tsum_eq Nat.pairEquiv.symm F
  rw [hreindex]
  -- Step F: Split ∑' p : ℕ × ℕ, F p = ∑' a, ∑' b, F (a, b) using Summable.tsum_prod
  have hF_summable : Summable F := by
    -- F p = ‖Tf‖²-style summand → summable since lp 2 has finite norm.
    -- Strategy: F (Nat.pairEquiv.symm n) = (Tf n)^2 (after formula),
    -- which is summable as a fiber of lp 2 (norm_rpow_eq_tsum).
    -- Use Equiv.summable_iff to transport.
    have hp : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
    have h_lp_sum : Summable (fun n : ℕ => ‖(Tf : ℕ → ℝ) n‖ ^ (2 : ENNReal).toReal) := by
      have := lp.memℓp Tf
      rwa [Memℓp, if_neg (by norm_num : (2 : ENNReal) ≠ 0),
           if_neg (by norm_num : (2 : ENNReal) ≠ ⊤)] at this
    have h_real : (fun n : ℕ => ‖(Tf : ℕ → ℝ) n‖ ^ (2 : ENNReal).toReal) =
        (fun n : ℕ => (Tf n) ^ 2) := by
      funext n
      simp only [show ((2 : ENNReal).toReal = 2) from by norm_num,
                 Real.norm_eq_abs, sq_abs]
    rw [h_real] at h_lp_sum
    -- After substituting cylinderMassOperator_formula, the (Tf n)^2 expression
    -- equals F (Nat.pairEquiv.symm n).
    have h_eq : (fun n : ℕ => (Tf n) ^ 2) = (fun n : ℕ => F (Nat.pairEquiv.symm n)) := by
      funext n
      show ((Tf : ℕ → ℝ) n) ^ 2 = F _
      rw [cylinderMassOperator_formula]
      simp [F, Nat.pairEquiv]
    rw [h_eq] at h_lp_sum
    exact (Equiv.summable_iff Nat.pairEquiv.symm).mp h_lp_sum
  rw [hF_summable.tsum_prod]
  -- Step G: Apply diagonal dm_parseval per spatial mode `a`.
  congr 1; funext a
  unfold perModeL2SqNorm
  -- ∑' b, (DM_b g)^2 = ∫ g^2 via dm_parseval f := g, g := g
  set g := resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
    (ntpSliceSchwartz L a f) with hg
  have h_parseval : ∑' n, DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) n g
        * DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) n g =
      ∫ x, g x * g x := dm_parseval g g
  -- The ∑' b, F (a, b) unfolds to ∑' b, (DM_b g)^2
  show ∑' b, F (a, b) = ∫ t, g t ^ 2
  have hunfold : ∀ b, F (a, b) =
      DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b g
        * DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b g := by
    intro b
    show (DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b g) ^ 2 = _
    ring
  simp_rw [hunfold]
  rw [h_parseval]
  congr 1; funext t; ring

/-! ## Step 4: Parametric main theorem

Given `S₂ : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ` that:
* commutes with each resolvent multiplier `R_{ω_a}`
* is L²-isometric on `SchwartzMap ℝ ℝ`
the tensor-mapped operator `nuclearTensorProduct_mapCLM id S₂` preserves
the mass operator ℓ²-norm.

This packages the full `id ⊗ S₂` argument once; both time reflection and
time translation discharge as one-line corollaries. -/

theorem cylinderMassOperator_norm_eq_of_temporal_action
    (mass : ℝ) (hmass : 0 < mass)
    (S₂ : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
    (h_R_comm : ∀ ω (hω : 0 < ω) (g : SchwartzMap ℝ ℝ),
      resolventMultiplierCLM hω (S₂ g) = S₂ (resolventMultiplierCLM hω g))
    (h_iso : ∀ g : SchwartzMap ℝ ℝ, ∫ t, (S₂ g) t ^ 2 = ∫ t, g t ^ 2)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass
        (nuclearTensorProduct_mapCLM
          (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂ f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ := by
  -- Show squared norms are equal, then take sqrt.
  have h_sq : ‖cylinderMassOperator L mass hmass
        (nuclearTensorProduct_mapCLM
          (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂ f)‖ ^ 2 =
      ‖cylinderMassOperator L mass hmass f‖ ^ 2 := by
    rw [cylinderMassOperator_normSq_eq_sum_perMode,
        cylinderMassOperator_normSq_eq_sum_perMode]
    -- Per-mode equality (proved below): perModeL2SqNorm a (Sf) = perModeL2SqNorm a f.
    congr 1; funext a
    -- LHS: ∫ (R_{ω_a}(slice_a (Sf)))²
    -- = ∫ (R_{ω_a}(S₂(slice_a f)))²    by ntpSliceSchwartz_tensorMap_id_left
    -- = ∫ (S₂(R_{ω_a}(slice_a f)))²    by h_R_comm
    -- = ∫ (R_{ω_a}(slice_a f))²        by h_iso
    unfold perModeL2SqNorm
    rw [ntpSliceSchwartz_tensorMap_id_left,
        h_R_comm _ (resolventFreq_pos L mass hmass a),
        h_iso]
  -- Take square roots (both sides are nonneg).
  have hx : (0 : ℝ) ≤ ‖cylinderMassOperator L mass hmass
      (nuclearTensorProduct_mapCLM
        (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂ f)‖ := norm_nonneg _
  have hy : (0 : ℝ) ≤ ‖cylinderMassOperator L mass hmass f‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖cylinderMassOperator L mass hmass
      (nuclearTensorProduct_mapCLM
        (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ)) S₂ f)‖
      - ‖cylinderMassOperator L mass hmass f‖), h_sq]

/-! ## Step 5: Concrete discharge — time reflection

`schwartzReflection` satisfies both hypotheses:
* commutes with `R_ω` because the resolvent symbol is even
  (`realFourierMultiplierCLM_even_reflection_comm` + `resolventSymbol_even`).
* is L²-isometric (`schwartzReflection_integral_sq`). -/

theorem cylinderMassOperator_timeReflection_norm_eq_proved
    (mass : ℝ) (hmass : 0 < mass) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderTimeReflection L f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ := by
  -- Unfold cylinderTimeReflection to its tensor-product form.
  show ‖cylinderMassOperator L mass hmass
        (nuclearTensorProduct_mapCLM
          (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
          schwartzReflection f)‖ =
        ‖cylinderMassOperator L mass hmass f‖
  apply cylinderMassOperator_norm_eq_of_temporal_action L mass hmass schwartzReflection
  · -- R_ω commutes with schwartzReflection (even resolvent symbol).
    intro ω hω g
    show resolventMultiplierCLM hω (schwartzReflection g) =
         schwartzReflection (resolventMultiplierCLM hω g)
    exact realFourierMultiplierCLM_even_reflection_comm (resolventSymbol ω)
      (resolventSymbol_hasTemperateGrowth ω hω) (resolventSymbol_even ω) g
  · -- schwartzReflection is L²-isometric.
    exact schwartzReflection_integral_sq

end GaussianField
