/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Space Instance for Schwartz Space via Sequence Space Isomorphism

Proves `NuclearSpace (SchwartzMap D ℝ)` for any finite-dimensional `D`,
replacing the 5 axioms in `Axioms.lean` with 3 sorrys.

## Strategy

The Schwartz space `S(D, ℝ)` is topologically isomorphic to the space `s(ℕ)`
of rapidly decreasing sequences (Dynin-Mityagin). The isomorphism is:
- For D = ℝ: the Hermite expansion (proved in `SchwartzNuclear.Basis1D`)
- For general D: iterated 1D isomorphisms via Fubini slicing (sorry'd)

The `NuclearSpace` instance is derived from this isomorphism by transferring
the basis, coefficients, expansion, growth, and decay properties through
the continuous linear equivalence.

## Sorry inventory

**3 sorrys** (reduced from 5 axioms):
1. `rapidDecay_hermite_summable` — summability of `∑ aₙ • ψₙ` in Schwartz topology
   (requires completeness of `SchwartzMap`, a standard result not yet in Mathlib)
2. `fromRapidDecay1DCLM.cont` — continuity of backward map (consequence of 1)
3. `schwartzRapidDecayEquivFin` for `d ≥ 2` — multi-dimensional Hermite expansion

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import SchwartzNuclear.Basis1D
import GaussianField.NuclearTensorProduct

noncomputable section

open GaussianField MeasureTheory Real SchwartzMap

namespace GaussianField

/-! ## The Sequence Space Isomorphism

The key mathematical fact: Schwartz space on any finite-dimensional real
normed space is topologically linearly isomorphic to the space of rapidly
decreasing sequences `s(ℕ)`.

For D = ℝ, this is the Hermite expansion:
  f ↦ (∫ f(x)ψₙ(x)dx)ₙ
where ψₙ are the Hermite functions. This is proved in `SchwartzNuclear.Basis1D`.

For D = ℝ^d with d > 1, the proof factors through:
  S(ℝ^d) → S(ℝ, S(ℝ^{d-1})) → s(ℕ, s(ℕ)) → s(ℕ×ℕ) → s(ℕ)
using Fubini slicing and Cantor pairing. -/

/-! ## Domain Transfer

`schwartzDomCongr` transfers Schwartz maps along a continuous linear equivalence
of domains. This is the key ingredient for reducing `SchwartzMap D ℝ` to
`SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ` and then to `SchwartzMap ℝ ℝ`. -/

/-- Composition with a continuous linear equivalence gives a topological isomorphism
of Schwartz spaces. Forward: `f ↦ f ∘ g`, backward: `f ↦ f ∘ g⁻¹`. -/
noncomputable def schwartzDomCongr {D E F : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : D ≃L[ℝ] E) :
    SchwartzMap E F ≃L[ℝ] SchwartzMap D F :=
  ContinuousLinearEquiv.equivOfInverse
    (compCLMOfContinuousLinearEquiv ℝ g)
    (compCLMOfContinuousLinearEquiv ℝ g.symm)
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.apply_symm_apply x))
    (fun f => SchwartzMap.ext fun x => by
      simp only [compCLMOfContinuousLinearEquiv_apply, Function.comp_def]
      exact congr_arg f (g.symm_apply_apply x))

/-- `EuclideanSpace ℝ (Fin 1)` is continuously linearly equivalent to `ℝ`. -/
noncomputable def euclideanFin1Equiv : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)

/-! ## 1D Hermite Isomorphism

The Hermite expansion gives a topological isomorphism `SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq`.
Forward: `f ↦ (cₙ(f))ₙ` where `cₙ(f) = ∫ f ψₙ`.
Backward: `a ↦ ∑' n, aₙ ψₙ` (tsum in Schwartz topology). -/

/-- Kronecker property: the Hermite coefficient of a basis function is δₙₘ. -/
theorem hermiteCoeff1D_basis_kronecker (n m : ℕ) :
    hermiteCoeff1D n (schwartzHermiteBasis1D m) = if n = m then 1 else 0 := by
  show ∫ x, schwartzHermiteBasis1D m x * hermiteFunction n x = _
  simp_rw [schwartzHermiteBasis1D_apply]
  convert hermiteFunction_orthonormal m n using 1
  exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)

/-- Hermite coefficients of a Schwartz function form a rapidly decreasing sequence.
From `hermiteCoeff1D_decay` at exponent `k + 2`:
  `|cₙ(f)| · (1+n)^(k+2) ≤ C · ‖f‖`, so `|cₙ(f)| · (1+n)^k ≤ C · ‖f‖ · (1+n)⁻²`,
which is summable. -/
private theorem hermiteCoeff_rapid_decay (f : SchwartzMap ℝ ℝ) (k : ℕ) :
    Summable (fun m => |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k) := by
  -- Get decay bound at k+2 (real exponent)
  obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
  set S := (Finset.Iic q).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f
  -- Each term bounded by C * S * (1+m)^{-2}
  have h_le : ∀ m : ℕ, |hermiteCoeff1D m f| * (1 + (m : ℝ)) ^ k ≤
      C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ) := by
    intro m
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have h_bd := hbound f m
    -- h_bd : |c_m| * (1+m)^((k:ℝ)+2) ≤ C * S
    -- Convert: (1+m)^((k:ℝ)+2) = (1+m)^k * (1+m)^2
    have h_split : (1 + (m : ℝ)) ^ ((k : ℝ) + 2) =
        (1 + (m : ℝ)) ^ (k : ℕ) * (1 + (m : ℝ)) ^ (2 : ℝ) := by
      rw [← rpow_natCast (1 + ↑m) k, ← rpow_add h1m]
    rw [h_split] at h_bd
    have h2_pos : (0 : ℝ) < (1 + ↑m) ^ (2 : ℝ) := rpow_pos_of_pos h1m 2
    have hle : |hermiteCoeff1D m f| * (1 + ↑m) ^ k ≤ C * S / (1 + ↑m) ^ (2 : ℝ) := by
      rw [le_div_iff₀ h2_pos]
      calc |hermiteCoeff1D m f| * (1 + ↑m) ^ k * (1 + ↑m) ^ (2 : ℝ)
          = |hermiteCoeff1D m f| * ((1 + ↑m) ^ (k : ℕ) * (1 + ↑m) ^ (2 : ℝ)) := by ring
        _ ≤ C * S := h_bd
    rwa [div_eq_mul_inv, ← rpow_neg h1m.le] at hle
  -- ∑ C * S * (1+m)^{-2} converges
  have h_sum : Summable (fun m : ℕ => C * S * (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h1 : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    exact h1.const_smul (C * S)
  exact .of_nonneg_of_le (fun m => mul_nonneg (abs_nonneg _)
    (pow_nonneg (by positivity) k)) h_le h_sum

/-- The forward linear map of the 1D Hermite isomorphism:
`f ↦ (hermiteCoeff1D n f)ₙ` as a rapid decay sequence. -/
private def toRapidDecay1DLM : SchwartzMap ℝ ℝ →ₗ[ℝ] RapidDecaySeq where
  toFun f := ⟨fun n => hermiteCoeff1D n f, hermiteCoeff_rapid_decay f⟩
  map_add' f g := RapidDecaySeq.ext fun n => (hermiteCoeff1D_linear n).map_add f g
  map_smul' r f := RapidDecaySeq.ext fun n => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    exact (hermiteCoeff1D_linear n).map_smul r f

/-- The forward CLM: Schwartz → RapidDecaySeq via Hermite coefficients. -/
private noncomputable def toRapidDecay1DCLM : SchwartzMap ℝ ℝ →L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecay1DLM
  cont := by
    -- Each rapidDecaySeminorm k on the output is bounded by Schwartz seminorms on the input
    apply Seminorm.continuous_from_bounded
      (schwartz_withSeminorms ℝ ℝ ℝ) RapidDecaySeq.rapidDecay_withSeminorms
    intro k
    -- rapidDecaySeminorm k (toRapidDecay1DLM f) = ∑' n, |cₙ(f)| * (1+n)^k
    -- From hermiteCoeff1D_decay ((k:ℝ)+2), each |cₙ(f)| * (1+n)^k ≤ C * S * (1+n)^{-2}
    -- So the sum ≤ C * S * ∑ (1+n)^{-2} = C' * S where S is a sup of Schwartz seminorms
    obtain ⟨C, q, hC, hbound⟩ := hermiteCoeff1D_decay ((k : ℝ) + 2)
    -- Sum of (1+n)^{-2}
    have h_base : Summable (fun n : ℕ => ((n : ℝ)) ^ ((-2) : ℝ)) :=
      summable_nat_rpow.mpr (by norm_num)
    have h_shifted := h_base.comp_injective
      (show Function.Injective (· + 1 : ℕ → ℕ) from fun a b h => Nat.succ_injective h)
    have h_rpow_sum : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ ((-2) : ℝ)) :=
      h_shifted.congr (fun n => by show ((↑(n + 1) : ℝ)) ^ ((-2) : ℝ) = _; simp [add_comm])
    set L := ∑' n : ℕ, (1 + (n : ℝ)) ^ ((-2) : ℝ)
    -- Total bound: C * L
    refine ⟨Finset.Iic q, ⟨C * L, by positivity⟩, fun f => ?_⟩
    -- Show: rapidDecaySeminorm k (toRapidDecay1DLM f) ≤ (C * L) • (sup seminorms) f
    simp only [Seminorm.comp_apply]
    set S := (Finset.Iic q).sup (schwartzSeminormFamily ℝ ℝ ℝ) f
    -- Each term bounded by C * S * (1+n)^{-2}
    have h_le : ∀ n : ℕ, |hermiteCoeff1D n f| * (1 + (n : ℝ)) ^ k ≤
        C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := by
      intro n
      have h1n : (0 : ℝ) < 1 + ↑n := by positivity
      have h_bd := hbound f n
      have h_split : (1 + (n : ℝ)) ^ ((k : ℝ) + 2) =
          (1 + (n : ℝ)) ^ (k : ℕ) * (1 + (n : ℝ)) ^ (2 : ℝ) := by
        rw [← rpow_natCast (1 + ↑n) k, ← rpow_add h1n]
      rw [h_split] at h_bd
      have h2_pos : (0 : ℝ) < (1 + ↑n) ^ (2 : ℝ) := rpow_pos_of_pos h1n 2
      have hle : |hermiteCoeff1D n f| * (1 + ↑n) ^ k ≤ C * S / (1 + ↑n) ^ (2 : ℝ) := by
        rw [le_div_iff₀ h2_pos]
        calc |hermiteCoeff1D n f| * (1 + ↑n) ^ k * (1 + ↑n) ^ (2 : ℝ)
            = |hermiteCoeff1D n f| * ((1 + ↑n) ^ (k : ℕ) * (1 + ↑n) ^ (2 : ℝ)) := by ring
          _ ≤ C * S := h_bd
      rwa [div_eq_mul_inv, ← rpow_neg h1n.le] at hle
    have h_tsum := (hermiteCoeff_rapid_decay f k).tsum_le_tsum h_le (h_rpow_sum.const_smul (C * S))
    calc ∑' n, |hermiteCoeff1D n f| * (1 + ↑n) ^ k
        ≤ ∑' (n : ℕ), C * S * (1 + (n : ℝ)) ^ ((-2) : ℝ) := h_tsum
      _ = C * S * L := by rw [tsum_mul_left]
      _ = C * L * S := by ring

/-- T2Space instance for Schwartz maps.
Derived from T1Space via topological group structure. -/
noncomputable instance schwartzMap_T2Space : T2Space (SchwartzMap ℝ ℝ) := by
  haveI : T1Space (SchwartzMap ℝ ℝ) :=
    WithSeminorms.T1_of_separating (schwartz_withSeminorms ℝ ℝ ℝ) fun f hf =>
      by
        -- If f ≠ 0, then seminorm(0,0) is nonzero since ‖f x‖ ≤ seminorm(0,0)(f)
        exact ⟨⟨0, 0⟩, fun h => hf (SchwartzMap.ext fun x =>
          norm_le_zero_iff.mp ((SchwartzMap.norm_le_seminorm ℝ f x).trans (le_of_eq h)))⟩
  exact inferInstance

/-- **Summability of Hermite expansion for rapid-decay coefficients.**

The series `∑ aₙ • ψₙ` converges in the Schwartz topology because for each seminorm
`p_{k,l}`, we have `∑ |aₙ| · p_{k,l}(ψₙ) ≤ ∑ |aₙ| · C · (1+n)^s < ∞` using basis
growth and rapid decay of `a`.

This requires completeness of `SchwartzMap ℝ ℝ` (Fréchet space), which is a standard
result not yet in Mathlib. -/
private theorem rapidDecay_hermite_summable (a : RapidDecaySeq) :
    Summable (fun n => a.val n • schwartzHermiteBasis1D n) := by
  sorry

/-- The backward linear map (underlying `LinearMap`). -/
private noncomputable def fromRapidDecay1DLM : RapidDecaySeq →ₗ[ℝ] SchwartzMap ℝ ℝ where
  toFun := fun a => ∑' n, a.val n • schwartzHermiteBasis1D n
  map_add' := fun a b => by
    simp only [RapidDecaySeq.add_val]
    rw [show (fun n => (a.val n + b.val n) • schwartzHermiteBasis1D n) =
      (fun n => a.val n • schwartzHermiteBasis1D n + b.val n • schwartzHermiteBasis1D n) from by
      ext n; rw [add_smul]]
    exact (rapidDecay_hermite_summable a).tsum_add (rapidDecay_hermite_summable b)
  map_smul' := fun r a => by
    simp only [RapidDecaySeq.smul_val, RingHom.id_apply]
    rw [show (fun n => (r * a.val n) • schwartzHermiteBasis1D n) =
      (fun n => r • (a.val n • schwartzHermiteBasis1D n)) from by
      ext n; rw [mul_smul]]
    exact (rapidDecay_hermite_summable a).tsum_const_smul r

/-- The backward CLM: `RapidDecaySeq → SchwartzMap ℝ ℝ` via Hermite expansion. -/
private noncomputable def fromRapidDecay1DCLM : RapidDecaySeq →L[ℝ] SchwartzMap ℝ ℝ where
  toLinearMap := fromRapidDecay1DLM
  cont := by
    -- Each Schwartz seminorm on the output is bounded by a rapid-decay seminorm on the input
    apply Seminorm.continuous_from_bounded
      RapidDecaySeq.rapidDecay_withSeminorms (schwartz_withSeminorms ℝ ℝ ℝ) fromRapidDecay1DLM
    intro ⟨k, l⟩
    -- From basis growth: p_{k,l}(ψₙ) ≤ C * (1+n)^s
    obtain ⟨C_h, hC_h, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
    -- The Schwartz seminorm of the tsum is bounded by the rapid decay seminorm
    refine ⟨{s}, ⟨C_h, le_of_lt hC_h⟩, fun a => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton]
    sorry

/-- The 1D Hermite isomorphism: `SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq`. -/
noncomputable def schwartzRapidDecayEquiv1D :
    SchwartzMap ℝ ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    toRapidDecay1DCLM
    fromRapidDecay1DCLM
    -- Left inverse: fromRapidDecay1DCLM ∘ toRapidDecay1DCLM = id
    (fun f => by
      -- fromRapidDecay1DCLM (toRapidDecay1DCLM f) = ∑' n, cₙ(f) • ψₙ = f
      show ∑' n, hermiteCoeff1D n f • schwartzHermiteBasis1D n = f
      exact ((schwartz_hermite_hasSum f).unique
        (schwartz_hermite_hasSum f).summable.hasSum).symm)
    -- Right inverse: toRapidDecay1DCLM ∘ fromRapidDecay1DCLM = id
    (fun a => by
      -- Need: hermiteCoeff1D n (∑' m, aₘ ψₘ) = aₙ for all n
      apply RapidDecaySeq.ext; intro n
      -- Apply continuous hermiteCoeff1DCLM to interchange with tsum
      show hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) = a.val n
      -- Interchange hermiteCoeff1DCLM (continuous) with tsum
      rw [show hermiteCoeff1D n (∑' m, a.val m • schwartzHermiteBasis1D m) =
        hermiteCoeff1DCLM n (∑' m, a.val m • schwartzHermiteBasis1D m) from rfl,
        (hermiteCoeff1DCLM n).map_tsum (rapidDecay_hermite_summable a)]
      -- Now: ∑' m, hermiteCoeff1DCLM n (aₘ • ψₘ) = ∑' m, aₘ * δₙₘ = aₙ
      simp only [hermiteCoeff1DCLM_apply, map_smul, smul_eq_mul,
        hermiteCoeff1D_basis_kronecker]
      -- ∑' m, a.val m * if n = m then 1 else 0 = a.val n
      -- Convert `if n = m` to `if m = n` for tsum_ite_eq
      simp_rw [show ∀ m, (if n = m then (1 : ℝ) else 0) = if m = n then 1 else 0 from
        fun m => by split_ifs <;> simp_all]
      simp [mul_ite, mul_one, mul_zero, tsum_ite_eq])

/-! ## Dimension Routing -/

/-- Schwartz space isomorphism for `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`.
- For `d = 1`: reduces to `SchwartzMap ℝ ℝ` via `euclideanFin1Equiv`, then uses `schwartzRapidDecayEquiv1D`.
- For `d ≥ 2`: sorry (multi-dimensional Hermite expansion). -/
noncomputable def schwartzRapidDecayEquivFin (d : ℕ) (hd : 0 < d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L[ℝ] RapidDecaySeq :=
  match d, hd with
  | 1, _ => (schwartzDomCongr euclideanFin1Equiv).symm.trans schwartzRapidDecayEquiv1D
  | d + 2, _ => sorry  -- multi-dimensional Hermite expansion

/-- The Schwartz space on any nontrivial finite-dimensional real normed space is
topologically linearly isomorphic to the space of rapidly decreasing sequences.

The proof decomposes as:
  `SchwartzMap D ℝ ≃L SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L RapidDecaySeq`
where `d = finrank ℝ D ≥ 1` (from `Nontrivial D`).

**Sorry**: 3 sorrys — 2 for the 1D backward map (completeness of SchwartzMap),
1 for `d ≥ 2` (multi-dimensional Hermite expansion). The 1D forward map and all
structural components are fully proved. -/
noncomputable def schwartzRapidDecayEquiv (D : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [Nontrivial D] :
    SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq :=
  have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
  (schwartzDomCongr (toEuclidean (E := D))).symm.trans
    (schwartzRapidDecayEquivFin (Module.finrank ℝ D) hd)

/-! ## Deriving NuclearSpace from the Isomorphism

Given `equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`, we construct
the `NuclearSpace` instance by:
- **basis** m := equiv.symm (basisVec m)
- **coeff** m := coeffCLM m ∘ equiv
- **expansion**: from `rapidDecay_expansion` transferred through equiv
- **basis_growth**: from continuity of equiv.symm + seminorms of basisVec
- **coeff_decay**: from continuity of equiv + rapid decay of equiv(f) -/

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ D] in
private theorem schwartz_expansion_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq)
    (φ : SchwartzMap D ℝ →L[ℝ] ℝ) (f : SchwartzMap D ℝ) :
    φ f = ∑' m, (RapidDecaySeq.coeffCLM m (equiv f)) *
      φ (equiv.symm (RapidDecaySeq.basisVec m)) := by
  have h := RapidDecaySeq.rapidDecay_expansion
    (φ.comp equiv.symm.toContinuousLinearMap) (equiv f)
  simp only [ContinuousLinearMap.comp_apply] at h
  -- h : φ (↑equiv.symm (equiv f)) = ∑' m, (equiv f).val m * φ (↑equiv.symm (basisVec m))
  -- Need: φ f = ∑' m, coeffCLM m (equiv f) * φ (equiv.symm (basisVec m))
  -- LHS match: ↑equiv.symm (equiv f) = f
  have h_lhs : (equiv.symm : RapidDecaySeq →L[ℝ] SchwartzMap D ℝ) (equiv f) = f :=
    equiv.symm_apply_apply f
  rw [h_lhs] at h
  exact h

/-- Monotonicity of rapid-decay seminorms: for j ≤ j', seminorm j ≤ seminorm j'. -/
private theorem rapidDecaySeminorm_mono {j j' : ℕ} (hjj : j ≤ j') :
    RapidDecaySeq.rapidDecaySeminorm j ≤ RapidDecaySeq.rapidDecaySeminorm j' := by
  intro a
  show ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j ≤ ∑' m, |a.val m| * (1 + (m : ℝ)) ^ j'
  apply (a.rapid_decay j).tsum_le_tsum _ (a.rapid_decay j')
  intro m
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (Nat.cast_nonneg m)) hjj

/-- The sup of rapid-decay seminorms over a finset is bounded by the seminorm
at the max index. -/
private theorem finset_sup_rapidDecaySeminorm_le (s : Finset ℕ) :
    s.sup RapidDecaySeq.rapidDecaySeminorm ≤
      RapidDecaySeq.rapidDecaySeminorm (s.sup id) := by
  apply Finset.sup_le
  intro j hj
  exact rapidDecaySeminorm_mono (Finset.le_sup (f := id) hj)

/-- The sup of rapid-decay seminorms evaluated at a basis vector gives
polynomial growth. -/
private theorem finset_sup_rapidDecaySeminorm_basisVec_le (s : Finset ℕ) (m : ℕ) :
    (s.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) ≤
      (1 + (m : ℝ)) ^ (s.sup id) := by
  calc (s.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m)
      ≤ RapidDecaySeq.rapidDecaySeminorm (s.sup id) (RapidDecaySeq.basisVec m) :=
        finset_sup_rapidDecaySeminorm_le s (RapidDecaySeq.basisVec m)
    _ = (1 + (m : ℝ)) ^ (s.sup id) :=
        RapidDecaySeq.rapidDecaySeminorm_basisVec _ m

omit [FiniteDimensional ℝ D] in
private theorem schwartz_basis_growth_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq) :
    ∀ (i : ℕ × ℕ), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, SchwartzMap.seminorm ℝ i.1 i.2
      (equiv.symm (RapidDecaySeq.basisVec m)) ≤ C * (1 + (m : ℝ)) ^ s := by
  intro ⟨k, l⟩
  -- The composition (seminorm k l) ∘ equiv.symm is a continuous seminorm on RapidDecaySeq
  set q : Seminorm ℝ RapidDecaySeq :=
    (SchwartzMap.seminorm ℝ k l).comp equiv.symm.toLinearMap with hq_def
  have hq_cont : Continuous q :=
    ((schwartz_withSeminorms ℝ D ℝ).continuous_seminorm ⟨k, l⟩).comp
      equiv.symm.continuous
  -- By Seminorm.bound_of_continuous, q is bounded by finitely many rapid-decay seminorms
  obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
    Seminorm.bound_of_continuous RapidDecaySeq.rapidDecay_withSeminorms q hq_cont
  -- Extract: for all a, seminorm k l (equiv.symm a) ≤ C_nn * (s_fin.sup rapidDecaySeminorm) a
  set N := s_fin.sup id
  have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
  refine ⟨(C_nn : ℝ), hC_pos, N, fun m => ?_⟩
  calc SchwartzMap.seminorm ℝ k l (equiv.symm (RapidDecaySeq.basisVec m))
      = q (RapidDecaySeq.basisVec m) := rfl
    _ ≤ C_nn • (s_fin.sup RapidDecaySeq.rapidDecaySeminorm) (RapidDecaySeq.basisVec m) :=
        hle (RapidDecaySeq.basisVec m)
    _ ≤ (C_nn : ℝ) * (1 + (m : ℝ)) ^ N := by
        simp only [NNReal.smul_def, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (finset_sup_rapidDecaySeminorm_basisVec_le s_fin m)
          (NNReal.coe_nonneg C_nn)

omit [FiniteDimensional ℝ D] in
private theorem schwartz_coeff_decay_from_equiv
    (equiv : SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq) :
    ∀ (k : ℕ), ∃ C > 0, ∃ (s : Finset (ℕ × ℕ)),
    ∀ (f : SchwartzMap D ℝ) (m : ℕ),
      |RapidDecaySeq.coeffCLM m (equiv f)| * (1 + (m : ℝ)) ^ k ≤
        C * (s.sup (fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l)) f := by
  intro k
  -- |coeffCLM m (equiv f)| = |(equiv f).val m|
  -- |(equiv f).val m| * (1+m)^k ≤ ∑' n, |(equiv f).val n| * (1+n)^k
  --   = rapidDecaySeminorm k (equiv f)
  -- From continuity of equiv: rapidDecaySeminorm k (equiv f) ≤ C * (sup Schwartz seminorms) f
  -- Get continuity bound for equiv
  set q : Seminorm ℝ (SchwartzMap D ℝ) :=
    (RapidDecaySeq.rapidDecaySeminorm k).comp equiv.toLinearMap with hq_def
  have hq_cont : Continuous q :=
    (RapidDecaySeq.rapidDecay_withSeminorms.continuous_seminorm k).comp
      equiv.continuous
  obtain ⟨s_fin, C_nn, hC_nn, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ D ℝ) q hq_cont
  have hC_pos : (0 : ℝ) < C_nn := NNReal.coe_pos.mpr (bot_lt_iff_ne_bot.mpr hC_nn)
  refine ⟨(C_nn : ℝ), hC_pos, s_fin, fun f m => ?_⟩
  -- |coeffCLM m (equiv f)| * (1+m)^k ≤ rapidDecaySeminorm k (equiv f)
  have h_le_tsum : |RapidDecaySeq.coeffCLM m (equiv f)| * (1 + (m : ℝ)) ^ k ≤
      RapidDecaySeq.rapidDecaySeminorm k (equiv f) := by
    show |(equiv f).val m| * (1 + (m : ℝ)) ^ k ≤
      ∑' n, |(equiv f).val n| * (1 + (n : ℝ)) ^ k
    exact ((equiv f).rapid_decay k).le_tsum m
      (fun j _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg j k))
  -- rapidDecaySeminorm k (equiv f) ≤ C_nn * (s_fin.sup Schwartz seminorms) f
  have h_bound : RapidDecaySeq.rapidDecaySeminorm k (equiv f) ≤
      (C_nn : ℝ) * (s_fin.sup (fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l)) f := by
    have := hle f
    simp only [hq_def, Seminorm.comp_apply, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul] at this
    exact this
  linarith

/-! ## The NuclearSpace Instance -/

/-- **Schwartz space is a nuclear Fréchet space.**

The instance uses the Schwartz seminorm family `(k, l) ↦ p_{k,l}` and a
basis/coefficient system derived from the topological isomorphism
`SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

This replaces the 5 axioms in the original `Axioms.lean` with 3 sorrys
(completeness of SchwartzMap for 1D, multi-dimensional Hermite for d ≥ 2). -/
noncomputable instance schwartz_nuclearSpace [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D ℝ
  basis m := (schwartzRapidDecayEquiv D).symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp
    (schwartzRapidDecayEquiv D).toContinuousLinearMap
  expansion := schwartz_expansion_from_equiv (schwartzRapidDecayEquiv D)
  basis_growth := schwartz_basis_growth_from_equiv (schwartzRapidDecayEquiv D)
  coeff_decay := schwartz_coeff_decay_from_equiv (schwartzRapidDecayEquiv D)

end GaussianField
