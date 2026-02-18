/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Space Instance for Schwartz Space via Sequence Space Isomorphism

Proves `NuclearSpace (SchwartzMap D ℝ)` for any finite-dimensional `D`,
replacing the 5 axioms in `Axioms.lean` with decomposed analytical sorrys.

## Strategy

The Schwartz space `S(D, ℝ)` is topologically isomorphic to the space `s(ℕ)`
of rapidly decreasing sequences (Dynin-Mityagin). The isomorphism is:
- For D = ℝ: the Hermite expansion (proved in `SchwartzNuclear.Basis1D`)
- For general D = ℝ^d: multi-index Hermite expansion using tensorized 1D
  Hermite functions indexed by `Fin d → ℕ`, flattened via a polynomially-bounded
  bijection `ℕ^d → ℕ`.

The `NuclearSpace` instance is derived from this isomorphism by transferring
the basis, coefficients, expansion, growth, and decay properties through
the continuous linear equivalence.

## Sorry inventory

**Sorrys** (reduced from 5 axioms):
- `multiIndexEquiv` — bijection `(Fin d → ℕ) ≃ ℕ` (combinatorial)
- `multiIndexEquiv_growth` / `multiIndexEquiv_symm_growth` — polynomial bounds
- `hermiteFunctionNd_decay` — Schwartz decay of tensor Hermite function (smoothness proved)
- `hermiteCoeffNd_decay` — rapid decay of multi-index Hermite coefficients
- `schwartzHermiteBasisNd_growth` — polynomial growth of basis seminorms
- `toRapidDecayNdCLM` / `fromRapidDecayNdCLM` — forward/backward CLMs
- `schwartzRapidDecayEquivNd` — left/right inverses

## References

- Dynin, Mityagin, "Criterion for nuclearity in terms of approximative dimension"
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import SchwartzNuclear.Basis1D
import GaussianField.NuclearTensorProduct

noncomputable section

open GaussianField MeasureTheory Real SchwartzMap
open scoped ContDiff

namespace GaussianField

/-! ## The Sequence Space Isomorphism

The key mathematical fact: Schwartz space on any finite-dimensional real
normed space is topologically linearly isomorphic to the space of rapidly
decreasing sequences `s(ℕ)`.

For D = ℝ, this is the Hermite expansion:
  f ↦ (∫ f(x)ψₙ(x)dx)ₙ
where ψₙ are the Hermite functions. This is proved in `SchwartzNuclear.Basis1D`.

For D = ℝ^d with d > 1, the proof uses multi-index Hermite expansion:
  f ↦ (∫ f(x) · ∏ᵢ ψ_{αᵢ}(xᵢ) dx)_α
flattened via a polynomially-bounded bijection `ℕ^d → ℕ`. -/

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

/-! ### Constructing the Schwartz limit of `∑ aₙ ψₙ`

For a rapid-decay sequence `a`, the pointwise series `g(x) = ∑' n, aₙ · ψₙ(x)` converges
(in ℝ, which is complete) and defines a Schwartz function. We construct it explicitly,
avoiding the need for `CompleteSpace (SchwartzMap ℝ ℝ)` (not yet in Mathlib). -/

/-- Bound on iterated derivative of `c * ψₙ`: `‖D^k(c·ψₙ)(x)‖ ≤ |c| · p_{0,k}(ψₙ)`. -/
private lemma scalar_hermite_iteratedFDeriv_bound (c : ℝ) (n k : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ k (fun y => c * hermiteFunction n y) x‖ ≤
    |c| * SchwartzMap.seminorm ℝ 0 k (schwartzHermiteBasis1D n) := by
  rw [show (fun y => c * hermiteFunction n y) =
    (fun y => c • hermiteFunction n y) from by ext; simp [smul_eq_mul]]
  rw [iteratedFDeriv_const_smul_apply' ((hermiteFunction_contDiff n k).contDiffAt),
    norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (by
    have h := SchwartzMap.le_seminorm ℝ 0 k (schwartzHermiteBasis1D n) x
    simp only [pow_zero, one_mul] at h
    rwa [show iteratedFDeriv ℝ k (⇑(schwartzHermiteBasis1D n)) x =
      iteratedFDeriv ℝ k (hermiteFunction n) x from
      congr_arg (iteratedFDeriv ℝ k · x) (schwartzHermiteBasis1D_coe n)] at h)
    (abs_nonneg _)

/-- Summability of `∑ |aₙ| · p_{k,l}(ψₙ)` for rapid-decay sequences.
Uses basis growth `p_{k,l}(ψₙ) ≤ C(1+n)^s` and rapid decay `∑ |aₙ|(1+n)^s < ∞`. -/
private lemma rapidDecay_seminorm_summable (a : RapidDecaySeq) (k l : ℕ) :
    Summable (fun n => |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)) := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (apply_nonneg _ _))
    (fun n => by
      calc |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n)
          ≤ |a.val n| * (C * (1 + ↑n) ^ s) :=
            mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _)
        _ = C * (|a.val n| * (1 + ↑n) ^ s) := by ring)
    (Summable.mul_left C (a.rapid_decay s))

/-- The pointwise tsum is smooth. -/
private lemma rapidDecay_hermite_contDiff (a : RapidDecaySeq) :
    ContDiff ℝ ∞ (fun x => ∑' n, a.val n * hermiteFunction n x) := by
  apply contDiff_tsum
    (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
  · intro n
    exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
  · intro j _; exact rapidDecay_seminorm_summable a 0 j
  · intro j n x _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j x

/-- Pointwise bound: `‖x‖^k · ‖D^l(∑' aₙψₙ)(x)‖ ≤ ∑' |aₙ| · p_{k,l}(ψₙ)`. -/
private lemma rapidDecay_pointwise_seminorm_le (a : RapidDecaySeq) (k l : ℕ) (x : ℝ) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤
    ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  -- Interchange iteratedFDeriv and tsum
  have h_iFD : iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x =
      ∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x := by
    apply iteratedFDeriv_tsum_apply (N := ⊤)
      (v := fun j n => |a.val n| * SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
    · intro n
      exact contDiff_infty.mpr (fun m => contDiff_const.mul (hermiteFunction_contDiff n m))
    · intro j _; exact rapidDecay_seminorm_summable a 0 j
    · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
    · exact le_top
  rw [h_iFD]
  -- Summability of norms
  have h_norm_summ : Summable (fun n =>
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
      (rapidDecay_seminorm_summable a 0 l)
  -- Pointwise bound: ‖x‖^k * ‖iteratedFDeriv(c*ψ_n)‖ ≤ |c| * p_{k,l}(ψ_n)
  have h_ptwise : ∀ n, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ ≤
      |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
    intro n
    have hfun_eq : (fun y => a.val n * hermiteFunction n y) =
        ⇑(a.val n • schwartzHermiteBasis1D n) := by
      ext y; simp [smul_eq_mul, schwartzHermiteBasis1D_apply]
    rw [hfun_eq]
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
        ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
          SchwartzMap.le_seminorm ℝ k l _ x
      _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
          rw [map_smul_eq_mul, Real.norm_eq_abs]
  -- Chain: ‖x‖^k * ‖tsum‖ ≤ tsum of bounds
  calc ‖x‖ ^ k * ‖∑' n, iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖
      ≤ ‖x‖ ^ k * ∑' n, ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
          (pow_nonneg (norm_nonneg _) k)
    _ = ∑' n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y => a.val n * hermiteFunction n y) x‖ :=
        tsum_mul_left.symm
    _ ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
        (Summable.of_nonneg_of_le
          (fun _ => mul_nonneg (pow_nonneg (norm_nonneg _) k) (norm_nonneg _))
          h_ptwise (rapidDecay_seminorm_summable a k l)).tsum_le_tsum
          h_ptwise (rapidDecay_seminorm_summable a k l)

/-- The pointwise tsum has Schwartz decay: `‖x‖^k · ‖D^l g(x)‖ ≤ C` uniformly. -/
private lemma rapidDecay_hermite_decay (a : RapidDecaySeq) (k l : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) x‖ ≤ C :=
  ⟨_, rapidDecay_pointwise_seminorm_le a k l⟩

/-- The Schwartz function defined by a rapid-decay Hermite expansion. -/
private noncomputable def rapidDecay_schwartzMap (a : RapidDecaySeq) : SchwartzMap ℝ ℝ where
  toFun := fun x => ∑' n, a.val n * hermiteFunction n x
  smooth' := rapidDecay_hermite_contDiff a
  decay' := rapidDecay_hermite_decay a

/-- Coercion: `rapidDecay_schwartzMap a` evaluates to the pointwise tsum. -/
private lemma rapidDecay_schwartzMap_apply (a : RapidDecaySeq) (x : ℝ) :
    rapidDecay_schwartzMap a x = ∑' n, a.val n * hermiteFunction n x := rfl

set_option maxHeartbeats 1600000 in
/-- The Hermite expansion converges to `rapidDecay_schwartzMap a` in Schwartz topology. -/
private theorem rapidDecay_hermite_hasSum (a : RapidDecaySeq) :
    HasSum (fun n => a.val n • schwartzHermiteBasis1D n) (rapidDecay_schwartzMap a) := by
  rw [HasSum]
  show Filter.Tendsto _ Filter.atTop _
  rw [(schwartz_withSeminorms ℝ ℝ ℝ).tendsto_nhds _ (rapidDecay_schwartzMap a)]
  intro ⟨k, l⟩ ε hε
  -- Get vanishing condition from summability of ∑ |aₙ| * p_{k,l}(ψₙ)
  have h_sem := rapidDecay_seminorm_summable a k l
  obtain ⟨s₀, hs₀⟩ := summable_iff_vanishing_norm.mp h_sem (ε / 2) (half_pos hε)
  rw [Filter.eventually_atTop]
  refine ⟨s₀, fun s hs => ?_⟩
  -- Flip subtraction order: (∑ - limit) = -(limit - ∑)
  rw [show (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) - rapidDecay_schwartzMap a =
    -(rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i) from by abel,
    map_neg_eq_map]
  -- Suffices to show seminorm(limit - partial sum) ≤ ε/2 < ε
  calc SchwartzMap.seminorm ℝ k l
        (rapidDecay_schwartzMap a - ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i)
      ≤ ε / 2 := by
        -- Reduce to pointwise bound via seminorm_le_bound
        apply SchwartzMap.seminorm_le_bound ℝ k l _ (half_pos hε).le
        intro x
        -- Set up notation
        set r := rapidDecay_schwartzMap a -
          ∑ i ∈ s, a.val i • schwartzHermiteBasis1D i with hr_def
        let g : ℕ → ℝ → ℝ := fun n y => a.val n * hermiteFunction n y
        -- Summability of iteratedFDeriv values
        have h_summ_iFD : Summable (fun n => iteratedFDeriv ℝ l (g n) x) := by
          apply Summable.of_norm_bounded
            (g := fun n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 l (schwartzHermiteBasis1D n))
          · exact rapidDecay_seminorm_summable a 0 l
          · intro n; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n l x
        -- Step 1: iteratedFDeriv of the limit = ∑' iteratedFDeriv(gₙ)
        have h_iFD_limit : iteratedFDeriv ℝ l
            (fun y => ∑' n, a.val n * hermiteFunction n y) x =
            ∑' n, iteratedFDeriv ℝ l (g n) x := by
          apply iteratedFDeriv_tsum_apply (N := ⊤)
            (v := fun j n => |a.val n| *
              SchwartzMap.seminorm ℝ 0 j (schwartzHermiteBasis1D n))
          · intro n
            exact contDiff_infty.mpr (fun m =>
              contDiff_const.mul (hermiteFunction_contDiff n m))
          · intro j _; exact rapidDecay_seminorm_summable a 0 j
          · intro j n y _; exact scalar_hermite_iteratedFDeriv_bound (a.val n) n j y
          · exact le_top
        -- Step 2: coercion of finite Schwartz sum = pointwise finite sum
        have hsum_coe : ∀ y,
            (∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
            ∑ i ∈ s, g i y := by
          intro y
          have : ∀ (t : Finset ℕ),
              (∑ i ∈ t, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) y =
              ∑ i ∈ t, g i y := by
            intro t; induction t using Finset.cons_induction with
            | empty => simp
            | cons a' t' ha' ih =>
              simp [SchwartzMap.smul_apply, smul_eq_mul, schwartzHermiteBasis1D_apply, g]
          exact this s
        -- Step 3: iteratedFDeriv of the finite sum
        have h_iFD_sum : iteratedFDeriv ℝ l
            (⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ)) x =
            ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
          have hcoe : ⇑(∑ i ∈ s, a.val i • schwartzHermiteBasis1D i : SchwartzMap ℝ ℝ) =
              fun y => ∑ i ∈ s, g i y := funext hsum_coe
          rw [hcoe]
          have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
            (fun i _ => (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          exact congr_fun h_eq x |>.trans (Finset.sum_apply x s _)
        -- Step 4: iteratedFDeriv of r = ∑'_{i∉s} iteratedFDeriv(gₙ)
        have h_iFD_r : iteratedFDeriv ℝ l (⇑r) x =
            ∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x := by
          have hf_cd : ContDiff ℝ l (fun y => ∑' n, a.val n * hermiteFunction n y) :=
            (rapidDecay_hermite_contDiff a).of_le (mod_cast le_top)
          have hg_cd : ContDiff ℝ l (fun y => ∑ i ∈ s, g i y) :=
            ContDiff.sum (fun i _ =>
              (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
          have hcoe_r : (⇑r : ℝ → ℝ) = fun y =>
              (∑' n, a.val n * hermiteFunction n y) - ∑ i ∈ s, g i y := by
            ext y; simp only [hr_def, SchwartzMap.sub_apply, rapidDecay_schwartzMap_apply]
            exact congrArg ((∑' n, a.val n * hermiteFunction n y) - ·) (hsum_coe y)
          rw [hcoe_r]
          set h_sum := fun y => ∑ i ∈ s, g i y with h_sum_def
          have h_neg_cd : ContDiff ℝ l (-h_sum) := hg_cd.neg
          have h_rw : (fun y => (∑' n, a.val n * hermiteFunction n y) - h_sum y) =
              (fun y => ∑' n, a.val n * hermiteFunction n y) + (-h_sum) := by
            ext; simp [sub_eq_add_neg]
          rw [h_rw, iteratedFDeriv_add hf_cd h_neg_cd, Pi.add_apply,
            iteratedFDeriv_neg, Pi.neg_apply, h_iFD_limit]
          have h_iFD_h : iteratedFDeriv ℝ l h_sum x =
              ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := by
            rw [h_sum_def]
            have h_eq := iteratedFDeriv_sum (𝕜 := ℝ) (f := g) (u := s) (i := l)
              (fun i _ =>
                (contDiff_const.mul (hermiteFunction_contDiff i l)).of_le le_rfl)
            calc iteratedFDeriv ℝ l (fun y => ∑ i ∈ s, g i y) x
                = (∑ j ∈ s, iteratedFDeriv ℝ l (g j)) x := congr_fun h_eq x
              _ = ∑ i ∈ s, iteratedFDeriv ℝ l (g i) x := Finset.sum_apply x s _
          rw [h_iFD_h]
          rw [← h_summ_iFD.sum_add_tsum_compl (s := s)]
          abel
        -- Summability on complement
        have h_norm_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            ‖iteratedFDeriv ℝ l (g ↑i) x‖) :=
          (Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
            (fun n => scalar_hermite_iteratedFDeriv_bound (a.val n) n l x)
            (rapidDecay_seminorm_summable a 0 l)).subtype _
        have h_sem_summ : Summable (fun (i : ↥(↑s : Set ℕ)ᶜ) =>
            |a.val ↑i| *
            SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
          (rapidDecay_seminorm_summable a k l).subtype _
        -- Key pointwise bound
        have h_ptwise : ∀ (i : ↥(↑s : Set ℕ)ᶜ),
            ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖ ≤
            |a.val ↑i| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i) := by
          intro ⟨n, _⟩
          have hg_eq : g n = ⇑(a.val n • schwartzHermiteBasis1D n) := by
            ext y; simp [g, smul_eq_mul, schwartzHermiteBasis1D_apply]
          rw [hg_eq]
          calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (⇑(a.val n • schwartzHermiteBasis1D n)) x‖
              ≤ SchwartzMap.seminorm ℝ k l (a.val n • schwartzHermiteBasis1D n) :=
                SchwartzMap.le_seminorm ℝ k l _ x
            _ = |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
                rw [map_smul_eq_mul, Real.norm_eq_abs]
        -- Chain the bounds
        rw [h_iFD_r]
        calc ‖x‖ ^ k * ‖∑' (i : ↥(↑s : Set ℕ)ᶜ), iteratedFDeriv ℝ l (g ↑i) x‖
            ≤ ‖x‖ ^ k * ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                ‖iteratedFDeriv ℝ l (g ↑i) x‖ :=
              mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm h_norm_summ)
                (pow_nonneg (norm_nonneg _) k)
          _ = ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (‖x‖ ^ k * ‖iteratedFDeriv ℝ l (g ↑i) x‖) := by
              rw [tsum_mul_left]
          _ ≤ ∑' (i : ↥(↑s : Set ℕ)ᶜ),
                (|a.val ↑i| *
                  SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D ↑i)) :=
              (h_norm_summ.mul_left _).tsum_le_tsum h_ptwise h_sem_summ
          _ ≤ ε / 2 := by
              apply h_sem_summ.tsum_le_of_sum_le
              intro t
              set t' := t.map ⟨Subtype.val, Subtype.val_injective⟩ with ht'_def
              have h_disj : Disjoint t' s := by
                rw [Finset.disjoint_left]
                intro n hn hn_s
                rw [Finset.mem_map] at hn
                obtain ⟨⟨m, hm⟩, _, rfl⟩ := hn
                exact hm hn_s
              have h_disj₀ : Disjoint t' s₀ := Disjoint.mono_right hs h_disj
              have h_lt := hs₀ t' h_disj₀
              rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ =>
                mul_nonneg (abs_nonneg _) (apply_nonneg _ _))] at h_lt
              rw [ht'_def, Finset.sum_map] at h_lt
              exact le_of_lt h_lt
    _ < ε := half_lt_self hε

/-- **Summability of Hermite expansion for rapid-decay coefficients.** -/
private theorem rapidDecay_hermite_summable (a : RapidDecaySeq) :
    Summable (fun n => a.val n • schwartzHermiteBasis1D n) :=
  ⟨_, rapidDecay_hermite_hasSum a⟩

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

/-- `fromRapidDecay1DLM a` equals `rapidDecay_schwartzMap a`. -/
private lemma fromRapidDecay1DLM_eq (a : RapidDecaySeq) :
    fromRapidDecay1DLM a = rapidDecay_schwartzMap a :=
  (rapidDecay_hermite_hasSum a).tsum_eq

/-- Seminorm bound: `p_{k,l}(fromRapidDecay1DLM a) ≤ ∑' n, |aₙ| * p_{k,l}(ψₙ)`. -/
private lemma fromRapidDecay1DLM_seminorm_le (a : RapidDecaySeq) (k l : ℕ) :
    SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
      ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) := by
  rw [fromRapidDecay1DLM_eq]
  exact SchwartzMap.seminorm_le_bound ℝ k l _ (tsum_nonneg fun n =>
    mul_nonneg (abs_nonneg _) (apply_nonneg _ _)) (rapidDecay_pointwise_seminorm_le a k l)

/-- Seminorm bound with rapid-decay seminorm: `p_{k,l}(Φ(a)) ≤ C * ρ_s(a)`. -/
private lemma fromRapidDecay1DLM_bound (k l : ℕ) :
    ∃ (C : ℝ), 0 < C ∧ ∃ (s : ℕ), ∀ (a : RapidDecaySeq),
      SchwartzMap.seminorm ℝ k l (fromRapidDecay1DLM a) ≤
        C * RapidDecaySeq.rapidDecaySeminorm s a := by
  obtain ⟨C, hC, s, hbasis⟩ := schwartzHermiteBasis1D_growth k l
  exact ⟨C, hC, s, fun a => by
    calc (SchwartzMap.seminorm ℝ k l) (fromRapidDecay1DLM a)
        ≤ ∑' n, |a.val n| * SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis1D n) :=
          fromRapidDecay1DLM_seminorm_le a k l
      _ ≤ ∑' n, |a.val n| * (C * (1 + (n : ℝ)) ^ s) :=
          (rapidDecay_seminorm_summable a k l).tsum_le_tsum
            (fun n => mul_le_mul_of_nonneg_left (hbasis n) (abs_nonneg _))
            ((a.rapid_decay s).mul_left C |>.congr fun n => by ring)
      _ = C * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ s := by
          rw [← tsum_mul_left]; congr 1; ext n; ring⟩

/-- The `IsBounded` property for `fromRapidDecay1DLM`: each Schwartz seminorm of the
output is bounded by a rapid-decay seminorm of the input. -/
private lemma fromRapidDecay1DLM_isBounded :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      (schwartzSeminormFamily ℝ ℝ ℝ) fromRapidDecay1DLM := by
  intro ⟨k, l⟩
  obtain ⟨C, hC, s, hbound⟩ := fromRapidDecay1DLM_bound k l
  exact ⟨{s}, ⟨C, hC.le⟩, fun a => by
    simp only [Seminorm.comp_apply, schwartzSeminormFamily, Finset.sup_singleton,
      Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact hbound a⟩

/-- The backward CLM: `RapidDecaySeq → SchwartzMap ℝ ℝ` via Hermite expansion. -/
private noncomputable def fromRapidDecay1DCLM : RapidDecaySeq →L[ℝ] SchwartzMap ℝ ℝ where
  toLinearMap := fromRapidDecay1DLM
  cont :=
    Seminorm.continuous_from_bounded RapidDecaySeq.rapidDecay_withSeminorms
      (schwartz_withSeminorms ℝ ℝ ℝ) fromRapidDecay1DLM fromRapidDecay1DLM_isBounded

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

/-! ## Multi-Dimensional Sequence Space and Flattening -/

/-- A multi-index is a function `Fin d → ℕ`. -/
abbrev MultiIndex (d : ℕ) := Fin d → ℕ

/-- The magnitude (L1 norm) of a multi-index. -/
def MultiIndex.abs {d : ℕ} (α : MultiIndex d) : ℕ :=
  ∑ i, α i

/-- To flatten s(ℕ^d) to s(ℕ), we need a bijection that is polynomially bounded
in both directions. We use iterated Cantor pairing: peel off the last coordinate
via `Fin.succFunEquiv`, recurse, then pair with `Nat.pairEquiv`. -/
noncomputable def multiIndexEquiv : (d : ℕ) → MultiIndex d ≃ ℕ
  | 0 => sorry -- Fin 0 → ℕ is a singleton, not bijectable with ℕ. Never used.
  | 1 => Equiv.funUnique (Fin 1) ℕ
  | (d + 2) => (Fin.succFunEquiv ℕ (d + 1)).trans
      ((Equiv.prodCongr (multiIndexEquiv (d + 1)) (Equiv.refl ℕ)).trans Nat.pairEquiv)

/-- Auxiliary: `multiIndexEquiv (d+2)` unfolds to pairing. -/
private lemma multiIndexEquiv_succ_apply (d : ℕ) (α : MultiIndex (d + 2)) :
    multiIndexEquiv (d + 2) α =
      Nat.pair (multiIndexEquiv (d + 1) ((Fin.succFunEquiv ℕ (d + 1) α).1))
        ((Fin.succFunEquiv ℕ (d + 1) α).2) := by
  simp [multiIndexEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Nat.pairEquiv]

/-- Auxiliary: `(multiIndexEquiv (d+2)).symm` unfolds through unpairing. -/
private lemma multiIndexEquiv_succ_symm (d : ℕ) (n : ℕ) :
    (multiIndexEquiv (d + 2)).symm n =
      (Fin.succFunEquiv ℕ (d + 1)).symm
        ((multiIndexEquiv (d + 1)).symm (Nat.unpair n).1, (Nat.unpair n).2) := by
  apply (multiIndexEquiv (d + 2)).injective
  simp only [Equiv.apply_symm_apply]
  rw [multiIndexEquiv_succ_apply]
  simp only [Equiv.apply_symm_apply, Nat.pair_unpair]

/-- Auxiliary: `MultiIndex.abs` decomposes along `Fin.succFunEquiv` for `d + 2`. -/
private lemma multiIndex_abs_succ (d : ℕ) (α : MultiIndex (d + 2)) :
    (MultiIndex.abs α : ℝ) =
      (MultiIndex.abs ((Fin.succFunEquiv ℕ (d + 1) α).1) : ℝ) +
        ((Fin.succFunEquiv ℕ (d + 1) α).2 : ℝ) := by
  simp only [MultiIndex.abs]
  push_cast
  rw [Fin.sum_univ_castSucc (n := d + 1)]
  congr 1

/-- Auxiliary: `MultiIndex.abs` of the inverse at `d+2` decomposes through unpairing. -/
private lemma multiIndex_abs_succ_symm (d : ℕ) (n : ℕ) :
    (MultiIndex.abs ((multiIndexEquiv (d + 2)).symm n) : ℝ) =
      (MultiIndex.abs ((multiIndexEquiv (d + 1)).symm (Nat.unpair n).1) : ℝ) +
        ((Nat.unpair n).2 : ℝ) := by
  rw [multiIndexEquiv_succ_symm]
  have h := multiIndex_abs_succ d
    ((Fin.succFunEquiv ℕ (d + 1)).symm
      ((multiIndexEquiv (d + 1)).symm (Nat.unpair n).1, (Nat.unpair n).2))
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- The multi-index enumeration has polynomial growth. -/
private lemma multiIndexEquiv_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ α : MultiIndex d,
      (1 + (multiIndexEquiv d α : ℝ)) ≤ C * (1 + (MultiIndex.abs α : ℝ)) ^ k := by
  induction d with
  | zero =>
    -- Fin 0 → ℕ is subsingleton; pick C large enough for the unique element
    refine ⟨1 + (multiIndexEquiv 0 Fin.elim0 : ℝ), by positivity, 0, fun α => ?_⟩
    have : α = Fin.elim0 := Subsingleton.elim α Fin.elim0
    subst this; simp
  | succ n ih =>
    match n, ih with
    | 0, _ =>
      -- d = 1: identity map
      refine ⟨1, one_pos, 1, fun α => ?_⟩
      simp only [multiIndexEquiv, Equiv.funUnique_apply, one_mul, pow_one]
      suffices h : (α default : ℝ) ≤ (MultiIndex.abs α : ℝ) by linarith
      gcongr
      show α default ≤ ∑ i, α i
      rw [Fin.default_eq_zero]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    | d + 1, ih =>
      -- d + 2: pairing with IH
      obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
      refine ⟨(C₁ + 1) ^ 2, by positivity, 2 * (k₁ + 1), fun α => ?_⟩
      rw [multiIndexEquiv_succ_apply]
      set β := (Fin.succFunEquiv ℕ (d + 1) α).1
      set a := (Fin.succFunEquiv ℕ (d + 1) α).2
      set m := multiIndexEquiv (d + 1) β
      have h_abs := multiIndex_abs_succ d α
      have h_pair_bound : (1 : ℝ) + ↑(Nat.pair m a) ≤ ((1 + ↑m) + ↑a) ^ 2 := by
        have h1 : Nat.pair m a < (max m a + 1) ^ 2 := Nat.pair_lt_max_add_one_sq m a
        have h2 : max m a + 1 ≤ m + a + 1 := by omega
        have h3 : (max m a + 1) ^ 2 ≤ (m + a + 1) ^ 2 := Nat.pow_le_pow_left h2 2
        have h4 : Nat.pair m a + 1 ≤ (m + a + 1) ^ 2 := by omega
        have h5 : ((Nat.pair m a + 1 : ℕ) : ℝ) ≤ (((m + a + 1) ^ 2 : ℕ) : ℝ) :=
          Nat.cast_le.mpr h4
        simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h5
        linarith
      have h_ih := hbound₁ β
      have h_one_abs : (1 : ℝ) ≤ 1 + (MultiIndex.abs α : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg _)
      have h_β_le : (1 + (MultiIndex.abs β : ℝ)) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
        linarith [h_abs, (show (0 : ℝ) ≤ ↑a from Nat.cast_nonneg a)]
      have h_a_le : (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) := by
        linarith [h_abs, (show (0 : ℝ) ≤ (MultiIndex.abs β : ℝ) from Nat.cast_nonneg _)]
      have h_sum : (1 + (m : ℝ)) + ↑a ≤ (C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
        have hm : (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
          calc (1 : ℝ) + ↑m ≤ C₁ * (1 + (MultiIndex.abs β : ℝ)) ^ k₁ := h_ih
            _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ k₁ := by
                apply mul_le_mul_of_nonneg_left _ hC₁.le
                exact pow_le_pow_left₀ (by positivity) h_β_le k₁
            _ ≤ C₁ * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
                apply mul_le_mul_of_nonneg_left _ hC₁.le
                exact pow_le_pow_right₀ h_one_abs (Nat.le_succ k₁)
        have ha : (a : ℝ) ≤ 1 * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) := by
          rw [one_mul]
          calc (a : ℝ) ≤ (1 + (MultiIndex.abs α : ℝ)) ^ 1 := by rw [pow_one]; exact h_a_le
            _ ≤ (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1) :=
                pow_le_pow_right₀ h_one_abs (by omega)
        linarith
      calc (1 : ℝ) + ↑(Nat.pair m a)
          ≤ ((1 + ↑m) + ↑a) ^ 2 := h_pair_bound
        _ ≤ ((C₁ + 1) * (1 + (MultiIndex.abs α : ℝ)) ^ (k₁ + 1)) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) h_sum
        _ = (C₁ + 1) ^ 2 * (1 + (MultiIndex.abs α : ℝ)) ^ (2 * (k₁ + 1)) := by
            rw [mul_pow]; ring_nf

/-- The inverse of the multi-index enumeration has polynomial growth. -/
private lemma multiIndexEquiv_symm_growth (d : ℕ) :
    ∃ C > 0, ∃ k : ℕ, ∀ n : ℕ,
      (1 + (MultiIndex.abs ((multiIndexEquiv d).symm n) : ℝ)) ≤ C * (1 + (n : ℝ)) ^ k := by
  induction d with
  | zero =>
    refine ⟨1, one_pos, 0, fun n => ?_⟩
    simp only [pow_zero, mul_one]
    have : (multiIndexEquiv 0).symm n = Fin.elim0 :=
      Subsingleton.elim _ Fin.elim0
    rw [this]; simp [MultiIndex.abs]
  | succ n ih =>
    match n, ih with
    | 0, _ =>
      -- d = 1: identity map
      refine ⟨1, one_pos, 1, fun n => ?_⟩
      simp only [multiIndexEquiv, one_mul, pow_one, MultiIndex.abs]
      show (1 : ℝ) + ↑((Equiv.funUnique (Fin 1) ℕ).symm n 0) ≤ 1 + ↑n
      simp [Equiv.funUnique]
    | d + 1, ih =>
      -- d + 2: unpairing with IH
      obtain ⟨C₁, hC₁, k₁, hbound₁⟩ := ih
      refine ⟨C₁ + 1, by linarith, k₁ + 1, fun n => ?_⟩
      rw [multiIndex_abs_succ_symm]
      set p := (Nat.unpair n).1
      set q := (Nat.unpair n).2
      have h_unpair : (p : ℝ) + ↑q ≤ ↑n := by
        exact_mod_cast Nat.unpair_add_le n
      have h_p_le : (p : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑q from Nat.cast_nonneg q]
      have h_q_le : (q : ℝ) ≤ ↑n := by linarith [show (0 : ℝ) ≤ ↑p from Nat.cast_nonneg p]
      have h_one_n : (1 : ℝ) ≤ 1 + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
      have h_ih := hbound₁ p
      have h_1p : (1 : ℝ) + ↑p ≤ 1 + ↑n := by linarith
      have h_beta : (1 : ℝ) + ↑(MultiIndex.abs ((multiIndexEquiv (d + 1)).symm p)) ≤
          C₁ * (1 + ↑n) ^ k₁ := by
        calc _ ≤ C₁ * (1 + ↑p) ^ k₁ := h_ih
          _ ≤ C₁ * (1 + ↑n) ^ k₁ := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_left₀ (by positivity) h_1p k₁
      calc (1 : ℝ) + (↑(MultiIndex.abs ((multiIndexEquiv (d + 1)).symm p)) + ↑q)
          ≤ C₁ * (1 + ↑n) ^ k₁ + ↑n := by linarith [h_beta, h_q_le]
        _ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) + (1 + ↑n) ^ (k₁ + 1) := by
            have hk : C₁ * (1 + ↑n) ^ k₁ ≤ C₁ * (1 + ↑n) ^ (k₁ + 1) := by
              apply mul_le_mul_of_nonneg_left _ hC₁.le
              exact pow_le_pow_right₀ h_one_n (Nat.le_succ k₁)
            have hn : (n : ℝ) ≤ (1 + ↑n) ^ (k₁ + 1) := by
              calc (n : ℝ) ≤ (1 + ↑n) ^ 1 := by rw [pow_one]; linarith
                _ ≤ (1 + ↑n) ^ (k₁ + 1) := pow_le_pow_right₀ h_one_n (by omega)
            linarith
        _ = (C₁ + 1) * (1 + ↑n) ^ (k₁ + 1) := by ring

/-! ## Multi-Dimensional Hermite Analysis -/

/-- The multidimensional Hermite function is the tensor product of 1D Hermite functions. -/
noncomputable def hermiteFunctionNd (d : ℕ) (α : MultiIndex d) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => ∏ i : Fin d, hermiteFunction (α i) (x i)

/-- Each factor `fun x => hermiteFunction (α i) (x i)` is smooth on `EuclideanSpace ℝ (Fin d)`. -/
private lemma hermiteFunctionNd_factor_contDiff (d : ℕ) (α : MultiIndex d) (i : Fin d) (m : ℕ) :
    ContDiff ℝ m (fun x : EuclideanSpace ℝ (Fin d) => hermiteFunction (α i) (x i)) :=
  (hermiteFunction_contDiff (α i) m).comp (contDiff_piLp_apply (p := 2))

/-- The multidimensional Hermite function is smooth. -/
private lemma hermiteFunctionNd_contDiff (d : ℕ) (α : MultiIndex d) :
    ContDiff ℝ ∞ (hermiteFunctionNd d α) := by
  apply contDiff_infty.mpr
  intro m
  exact contDiff_prod (fun i _ => hermiteFunctionNd_factor_contDiff d α i m)

/-- The multidimensional Hermite function has Schwartz decay.

The proof uses the product structure: each 1D factor `hermiteFunction (α i)` is Schwartz,
so for any `k`, the factor at coordinate `i` satisfies `|x_i|^k * |D^m ψ_{α_i}(x_i)| ≤ C`.
The `iteratedFDeriv` of the product decomposes via the multilinear Leibniz rule into sums of
products of individual derivatives. Each term has at most one "active" coordinate that absorbs
the `‖x‖^k` factor through Schwartz decay, while all other coordinates contribute bounded
derivative values. -/
private lemma hermiteFunctionNd_decay (d : ℕ) (α : MultiIndex d) (k n : ℕ) :
    ∃ C : ℝ, ∀ x : EuclideanSpace ℝ (Fin d),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (hermiteFunctionNd d α) x‖ ≤ C := by
  sorry

/-- The multidimensional Hermite function as a Schwartz map. -/
noncomputable def schwartzHermiteBasisNd (d : ℕ) (α : MultiIndex d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ where
  toFun := hermiteFunctionNd d α
  smooth' := hermiteFunctionNd_contDiff d α
  decay' := hermiteFunctionNd_decay d α

/-- The coefficient of a Schwartz function against a multidimensional Hermite function. -/
noncomputable def hermiteCoeffNd (d : ℕ) (α : MultiIndex d)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) : ℝ :=
  ∫ x, f x * hermiteFunctionNd d α x

/-- Multidimensional Hermite coefficients decay rapidly.
This is the multivariate generalization of `hermiteCoeff1D_decay`, proved via
multivariate integration by parts. -/
private lemma hermiteCoeffNd_decay (d : ℕ) (k : ℝ) :
    ∃ (C : ℝ) (q : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) (α : MultiIndex d),
        |hermiteCoeffNd d α f| * (1 + (MultiIndex.abs α : ℝ)) ^ k ≤
          C * q.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin d)) ℝ) f := sorry

/-- The multidimensional Hermite basis functions have polynomial growth in seminorms. -/
private lemma schwartzHermiteBasisNd_growth (d : ℕ) (k l : ℕ) :
    ∃ (C : ℝ) (hC : 0 < C) (s : ℕ), ∀ (α : MultiIndex d),
      SchwartzMap.seminorm ℝ k l (schwartzHermiteBasisNd d α) ≤
        C * (1 + (MultiIndex.abs α : ℝ)) ^ s := sorry

/-! ## Multi-Dimensional Isomorphism -/

/-- The forward continuous linear map for the d-dimensional Hermite expansion.
Maps `S(ℝ^d)` to `s(ℕ)` using the flattened multi-index. -/
noncomputable def toRapidDecayNdCLM (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ →L[ℝ] RapidDecaySeq :=
  sorry -- Relies on `hermiteCoeffNd_decay` and `multiIndexEquiv_symm_growth`.

/-- The backward continuous linear map for the d-dimensional Hermite expansion.
Maps `s(ℕ)` to `S(ℝ^d)`. -/
noncomputable def fromRapidDecayNdCLM (d : ℕ) :
    RapidDecaySeq →L[ℝ] SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ :=
  sorry -- Relies on `schwartzHermiteBasisNd_growth` and `multiIndexEquiv_growth`.

/-- The d-dimensional Hermite topological isomorphism. -/
noncomputable def schwartzRapidDecayEquivNd (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    (toRapidDecayNdCLM d)
    (fromRapidDecayNdCLM d)
    sorry -- Left inverse (pointwise convergence of multidimensional Hermite series)
    sorry -- Right inverse (orthonormality of the multidimensional basis)

/-- Schwartz space isomorphism for `EuclideanSpace ℝ (Fin d)` with `d ≥ 1`.
- For `d = 1`: reduces to `SchwartzMap ℝ ℝ` via `euclideanFin1Equiv`,
  then uses `schwartzRapidDecayEquiv1D`.
- For `d ≥ 2`: uses the generalized `schwartzRapidDecayEquivNd`. -/
noncomputable def schwartzRapidDecayEquivFin (d : ℕ) (hd : 0 < d) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L[ℝ] RapidDecaySeq :=
  match d, hd with
  | 1, _ => (schwartzDomCongr euclideanFin1Equiv).symm.trans schwartzRapidDecayEquiv1D
  | d + 2, _ => schwartzRapidDecayEquivNd (d + 2)

/-- The Schwartz space on any nontrivial finite-dimensional real normed space is
topologically linearly isomorphic to the space of rapidly decreasing sequences.

The proof decomposes as:
  `SchwartzMap D ℝ ≃L SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ ≃L RapidDecaySeq`
where `d = finrank ℝ D ≥ 1` (from `Nontrivial D`).

**Sorry**: sorrys for `d ≥ 2` are decomposed into multi-index Hermite analysis components.
The 1D forward and backward maps and all structural components are fully proved. -/
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

This replaces the 5 axioms in the original `Axioms.lean` with decomposed
sorrys for multi-dimensional Hermite analysis (d ≥ 2). -/
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
