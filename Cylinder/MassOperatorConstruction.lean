/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass Operator Construction

Constructs the cylinder mass operator `T : CylinderTestFunction L →L[ℝ] ell2'`
as a concrete definition, replacing the axiom in `Cylinder/GreenFunction.lean`.

## Construction

The mass operator acts on a cylinder test function `f` by:
1. Extracting the a-th spatial DM mode via `ntpSliceSchwartz L a f : SchwartzMap ℝ ℝ`
2. Applying the resolvent multiplier `R_{ω_a}` with symbol `(p² + ω_a²)^{-1/2}`
3. Taking the b-th temporal DM (Hermite) coefficient
4. Indexing the result by `m = Nat.pair a b`

The resulting sequence is in ℓ² because:
- The resolvent multiplier is a bounded CLM on 𝓢(ℝ)
- The Hermite coefficients of a Schwartz function are rapidly decaying
- The slice extraction is also rapidly decaying in a

## Main definitions

- `resolventFreq L mass n` — dispersion relation ω_n = √(λ_n + m²)
- `massOperatorCoord L mass hmass m` — the m-th coordinate functional
- `cylinderMassOperator L mass hmass` — the mass operator as a CLM

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Cylinder.FreeHeatSemigroup
import Cylinder.PositiveTime
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Resolvent frequency (dispersion relation)

For each spatial Fourier mode n on S¹_L with eigenvalue λ_n = (2πk/L)²,
the dispersion relation gives the effective mass:

  `ω_n = √(λ_n + m²) = √((2πk/L)² + m²)`

This is the frequency that appears in the temporal resolvent kernel
`exp(-ω_n|t|)/(2ω_n)` and determines the mass gap of the theory. -/

/-- **Dispersion relation on the cylinder.**

  `ω_n = √((2πk/L)² + m²)`

where `k = fourierFreq(n)` is the spatial frequency of the n-th Fourier
mode on S¹_L. This is the resolvent frequency for the 1D operator
`-d²/dt² + ω_n²` acting on the temporal Schwartz functions. -/
def resolventFreq (mass : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2)

omit hL in
/-- The resolvent frequency is strictly positive when mass > 0. -/
theorem resolventFreq_pos (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    0 < resolventFreq L mass n := by
  unfold resolventFreq
  apply Real.sqrt_pos_of_pos
  positivity

omit hL in
/-- The square of the resolvent frequency recovers the spatial eigenvalue + mass². -/
theorem resolventFreq_sq (mass : ℝ) (n : ℕ) :
    resolventFreq L mass n ^ 2 =
    (2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2 := by
  unfold resolventFreq
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit hL in
/-- The resolvent frequency is nonneg. -/
theorem resolventFreq_nonneg (mass : ℝ) (n : ℕ) :
    0 ≤ resolventFreq L mass n := by
  unfold resolventFreq
  exact Real.sqrt_nonneg _

omit hL in
/-- The resolvent frequency is at least the mass. -/
theorem resolventFreq_mass_le (mass : ℝ) (hmass : 0 ≤ mass) (n : ℕ) :
    mass ≤ resolventFreq L mass n := by
  unfold resolventFreq
  calc mass = Real.sqrt (mass ^ 2) := (Real.sqrt_sq hmass).symm
    _ ≤ Real.sqrt ((2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2) := by
        apply Real.sqrt_le_sqrt; linarith [sq_nonneg (2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L)]

omit hL in
/-- The zero mode (n=0) has resolvent frequency equal to the mass. -/
theorem resolventFreq_zero_mode (mass : ℝ) (hmass : 0 ≤ mass) :
    resolventFreq L mass 0 = mass := by
  unfold resolventFreq
  simp [SmoothMap_Circle.fourierFreq, Real.sqrt_sq hmass]

/-! ## Coordinate functionals

The m-th coordinate of the mass operator output is:
  `(T f)_m = coeff_b(R_{ω_a}(slice_a(f)))`
where `(a, b) = Nat.unpair m`. -/

/-- The m-th coordinate functional of the mass operator.

For `m` with `(a, b) = Nat.unpair m`, this is the composition:
  `f ↦ coeff_b(R_{ω_a}(ntpSliceSchwartz L a f))`

This is a CLM `CylinderTestFunction L →L[ℝ] ℝ` as a composition of three CLMs:
- `ntpSliceSchwartz L a : CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ`
- `resolventMultiplierCLM hω : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ`
- `DyninMityaginSpace.coeff b : SchwartzMap ℝ ℝ →L[ℝ] ℝ` -/
def massOperatorCoord (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    CylinderTestFunction L →L[ℝ] ℝ :=
  let a := (Nat.unpair m).1
  let b := (Nat.unpair m).2
  let hω := resolventFreq_pos L mass hmass a
  (DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b).comp
    ((resolventMultiplierCLM hω).comp (ntpSliceSchwartz L a))

/-- The coordinate functional is the composition of slice, resolvent, and coeff. -/
theorem massOperatorCoord_apply (mass : ℝ) (hmass : 0 < mass) (m : ℕ)
    (f : CylinderTestFunction L) :
    massOperatorCoord L mass hmass m f =
    DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) (Nat.unpair m).2
      (resolventMultiplierCLM (resolventFreq_pos L mass hmass (Nat.unpair m).1)
        (ntpSliceSchwartz L (Nat.unpair m).1 f)) := rfl

/-! ## Decay bound

The key technical estimate: the coordinate functionals decay like `(1+m)^{-2}`,
which ensures the output sequence is in ℓ².

### Proof outline

For `m` with `(a, b) = Nat.unpair m`, the coordinate functional is:
  `massOperatorCoord m f = coeff_b(R_{ω_a}(slice_a(f)))`

The `(1+m)^{-2}` decay combines `(1+a)^{-4}` and `(1+b)^{-4}` decay via
the Cantor pairing bound `(1+m) ≤ (1+a)²(1+b)²`:

1. **b-decay from coeff_decay**: `|coeff_b(g)| * (1+b)^4 ≤ C₁ · q(g)`
   for any SchwartzMap g, by `DyninMityaginSpace.coeff_decay` at exponent 4.

2. **Resolvent uniform bound**: `q(R_{ω_a}(h)) ≤ C₂ · r(h)` uniformly in a,
   because the resolvent symbol `(p² + ω²)^{-1/2}` is pointwise decreasing in ω
   and `ω_a ≥ mass > 0` for all a.

3. **a-decay from slice extraction**: `r(slice_a(f)) ≤ C₃ · p(f) · (1+a)^{-4}`
   using higher DM seminorms of f. The rapid decay `|f.val(pair(a,b))| * (1+pair(a,b))^j
   ≤ seminorm_j(f)` and `pair(a,b) ≥ a` give the a-decay.

4. **Cantor pairing**: `(1+a)^{-4} · (1+b)^{-4} ≤ (1+m)^{-2}` since
   `(1+m)² ≤ (1+a)⁴ · (1+b)⁴`. -/

/-- Cantor pairing bound: `1 + pair(a,b) ≤ (1+a)² · (1+b)²`.

Proof: `pair(a,b) + 1 ≤ (a+b+1)²` (by omega) and `a+b+1 ≤ (1+a)(1+b)` (since `ab ≥ 0`). -/
private theorem one_add_pair_le (a b : ℕ) :
    (1 + (Nat.pair a b : ℝ)) ≤ (1 + (a : ℝ)) ^ 2 * (1 + (b : ℝ)) ^ 2 := by
  have h1 : Nat.pair a b + 1 ≤ (a + b + 1) * (a + b + 1) := by
    unfold Nat.pair; split <;> nlinarith
  have h2 : (1 : ℝ) + (Nat.pair a b : ℝ) ≤ ((a : ℝ) + b + 1) ^ 2 := by
    have := Nat.cast_le (α := ℝ).mpr h1; push_cast at this ⊢; nlinarith
  have h3 : ((a : ℝ) + b + 1) ≤ (1 + (a : ℝ)) * (1 + (b : ℝ)) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]
  have h4 : ((a : ℝ) + b + 1) ^ 2 ≤ ((1 + (a : ℝ)) * (1 + (b : ℝ))) ^ 2 :=
    sq_le_sq' (by nlinarith [Nat.cast_nonneg (α := ℝ) a, Nat.cast_nonneg (α := ℝ) b]) h3
  linarith [mul_pow (1 + (a : ℝ)) (1 + (b : ℝ)) 2]

/-- `(1+m)² ≤ (1+a)⁴ · (1+b)⁴` for `m = pair(a,b)`.
Squaring `one_add_pair_le`. -/
private theorem pair_decay_bound_pow (a b : ℕ) :
    (1 + (Nat.pair a b : ℝ)) ^ 2 ≤ (1 + (a : ℝ)) ^ 4 * (1 + (b : ℝ)) ^ 4 :=
  calc (1 + (Nat.pair a b : ℝ)) ^ 2
      ≤ ((1 + (a : ℝ)) ^ 2 * (1 + (b : ℝ)) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (one_add_pair_le a b) 2
    _ = (1 + (a : ℝ)) ^ 4 * (1 + (b : ℝ)) ^ 4 := by ring

/-- The resolvent multiplier conjugated to RDS has RDS seminorm bounds uniform
in `ω ≥ mass > 0`.

The CLM `Φ_ω := equiv ∘ R_ω ∘ equiv⁻¹ : RapidDecaySeq →L[ℝ] RapidDecaySeq`
has `IsBounded` with constants independent of `ω` for `ω ≥ mass`.

This holds because:
1. `equiv` and `equiv⁻¹` are fixed CLEs (constant bounds)
2. The resolvent symbol `(p² + ω²)^{-1/2}` is pointwise decreasing in ω,
   so the Schwartz seminorm bounds at `ω = mass` dominate those at any ω ≥ mass

Reference: Stein, *Singular Integrals*, Ch. VI — Fourier multiplier seminorm
bounds depend on symbol derivatives, which decrease for the resolvent as ω grows.
Glimm-Jaffe §6.1: the resolvent family `{R_ω : ω ≥ mass}` is uniformly bounded
on 𝓢(ℝ). -/
axiom resolventRDS_uniformBound
    (mass : ℝ) (hmass : 0 < mass) (k : ℕ) :
    ∃ (s : Finset ℕ) (C : ℝ) (_ : 0 < C),
    ∀ (n : ℕ) (g : RapidDecaySeq),
      RapidDecaySeq.rapidDecaySeminorm k
        (schwartzRapidDecayEquiv1D
          (resolventMultiplierCLM (resolventFreq_pos L mass hmass n)
            (schwartzRapidDecayEquiv1D.symm g))) ≤
      C * (s.sup RapidDecaySeq.rapidDecaySeminorm) g

/-- Slice extraction with `a`-decay: the k-th RDS seminorm of `slice_a f` decays
like `(1+a)^{-j₁}` using higher RDS seminorms of `f`.

Uses `|f.val(pair(a,b))| * (1+pair(a,b))^j ≤ rapidDecaySeminorm j f` and
`(1+pair(a,b))^{j₁+j₂} ≥ (1+a)^{j₁} · (1+b)^{j₂}` to split the decay. -/
private theorem ntpExtractSlice_a_decay (a : ℕ) (k j₁ : ℕ) (f : RapidDecaySeq) :
    RapidDecaySeq.rapidDecaySeminorm k (ntpExtractSlice a f) ≤
    (∑' (n : ℕ), ((1 + (n : ℝ)) ^ 2)⁻¹) *
    RapidDecaySeq.rapidDecaySeminorm (k + j₁ + 2) f *
    ((1 + (a : ℝ)) ^ j₁)⁻¹ := by
  show ∑' b, |f.val (Nat.pair a b)| * (1 + ↑b) ^ k ≤ _
  set j := k + j₁ + 2
  have h_term : ∀ b : ℕ,
      |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k ≤
      RapidDecaySeq.rapidDecaySeminorm j f *
      ((1 + (a : ℝ)) ^ j₁)⁻¹ * ((1 + (b : ℝ)) ^ 2)⁻¹ := by
    intro b
    have h_coeff : |f.val (Nat.pair a b)| * (1 + (Nat.pair a b : ℝ)) ^ j ≤
        RapidDecaySeq.rapidDecaySeminorm j f :=
      (f.rapid_decay j).le_tsum (Nat.pair a b)
        (fun n _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg n j))
    have ha_le : (1 + (a : ℝ)) ≤ (1 + (Nat.pair a b : ℝ)) := by
      have := Nat.cast_le (α := ℝ).mpr (Nat.left_le_pair a b); linarith
    have h_split : (1 + (b : ℝ)) ^ k * (1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2 ≤
        (1 + (Nat.pair a b : ℝ)) ^ j := by
      calc (1 + (b : ℝ)) ^ k * (1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2
          = (1 + (b : ℝ)) ^ k * ((1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2) := by ring
        _ ≤ (1 + (Nat.pair a b : ℝ)) ^ k *
            ((1 + (Nat.pair a b : ℝ)) ^ j₁ * (1 + (Nat.pair a b : ℝ)) ^ 2) := by
          apply mul_le_mul (pair_weight_le a b k) _ (by positivity) (by positivity)
          apply mul_le_mul (pow_le_pow_left₀ (by positivity) ha_le j₁)
            (pair_weight_le a b 2) (by positivity) (by positivity)
        _ = (1 + (Nat.pair a b : ℝ)) ^ (k + j₁ + 2) := by ring
    rw [show RapidDecaySeq.rapidDecaySeminorm j f *
        ((1 + (a : ℝ)) ^ j₁)⁻¹ * ((1 + (b : ℝ)) ^ 2)⁻¹ =
        RapidDecaySeq.rapidDecaySeminorm j f /
        ((1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2) from by
      rw [div_eq_mul_inv, mul_inv]; ring]
    rw [le_div_iff₀ (by positivity)]
    calc |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k *
          ((1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2)
        = |f.val (Nat.pair a b)| * ((1 + (b : ℝ)) ^ k *
          (1 + (a : ℝ)) ^ j₁ * (1 + (b : ℝ)) ^ 2) := by ring
      _ ≤ |f.val (Nat.pair a b)| * (1 + (Nat.pair a b : ℝ)) ^ j :=
          mul_le_mul_of_nonneg_left h_split (abs_nonneg _)
      _ ≤ RapidDecaySeq.rapidDecaySeminorm j f := h_coeff
  have h_rhs_summable : Summable (fun b : ℕ =>
      RapidDecaySeq.rapidDecaySeminorm j f *
      ((1 + (a : ℝ)) ^ j₁)⁻¹ * ((1 + (b : ℝ)) ^ 2)⁻¹) :=
    NuclearTensorProduct.summable_inv_one_add_sq.mul_left _
  have h_lhs_summable := (ntpExtractSlice a f).rapid_decay k
  calc ∑' (b : ℕ), |f.val (Nat.pair a b)| * (1 + (b : ℝ)) ^ k
      ≤ ∑' (b : ℕ), (RapidDecaySeq.rapidDecaySeminorm j f *
          ((1 + (a : ℝ)) ^ j₁)⁻¹ * ((1 + (b : ℝ)) ^ 2)⁻¹) :=
        Summable.tsum_le_tsum h_term h_lhs_summable h_rhs_summable
    _ = RapidDecaySeq.rapidDecaySeminorm j f * ((1 + (a : ℝ)) ^ j₁)⁻¹ *
        ∑' (b : ℕ), ((1 + (b : ℝ)) ^ 2)⁻¹ := tsum_mul_left ..
    _ = (∑' (n : ℕ), ((1 + (n : ℝ)) ^ 2)⁻¹) *
        RapidDecaySeq.rapidDecaySeminorm (k + j₁ + 2) f *
        ((1 + (a : ℝ)) ^ j₁)⁻¹ := by ring

theorem massOperatorCoord_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (DyninMityaginSpace.ι (E := CylinderTestFunction L))) (C : ℝ) (_ : 0 < C),
    ∀ (m : ℕ) (f : CylinderTestFunction L),
      |massOperatorCoord L mass hmass m f| ≤
      (C * (s.sup DyninMityaginSpace.p) f) * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
  -- Step 1: resolvent uniform RDS bound at seminorm index 4
  obtain ⟨s_R, C_R, hC_R, h_resolvent⟩ := resolventRDS_uniformBound L mass hmass 4
  -- Step 2: Define the total seminorm index
  -- The slice decay uses rapidDecaySeminorm at index (sup(s_R) + 4 + 2) where sup(s_R)
  -- is the max index needed by the resolvent bound.
  -- For each k ∈ s_R, we need ntpExtractSlice_a_decay at (k, j₁ = 4)
  -- which uses rapidDecaySeminorm (k + 4 + 2) = rapidDecaySeminorm (k + 6)
  -- Set s_total = {k + 6 | k ∈ s_R}
  set Z := ∑' (n : ℕ), ((1 + (n : ℝ)) ^ 2)⁻¹ with hZ
  have hZ_pos : 0 < Z := by
    exact NuclearTensorProduct.summable_inv_one_add_sq.tsum_pos
      (fun n => by positivity) 0 (by positivity)
  -- For the bound we need a single finset. We compose:
  -- |massOperatorCoord m f| ≤ C_total * (s_total.sup p) f * (1+a)^{-4} * (1+b)^{-4}
  -- ≤ C_total * (s_total.sup p) f * (1+m)^{-2}
  -- where (a, b) = Nat.unpair m
  --
  -- The chain:
  -- |massOperatorCoord m f| = |(equiv(R(slice_a f))).val b|
  -- ≤ rapidDecaySeminorm 4 (equiv(R(slice_a f))) / (1+b)^4
  -- ≤ C_R * (s_R.sup rapidDecaySeminorm)(slice_a f) / (1+b)^4   [resolvent bound, uniform]
  -- ≤ C_R * Σ_{k∈s_R} rapidDecaySeminorm k (slice_a f) / (1+b)^4
  -- ≤ C_R * Σ_{k∈s_R} Z * rapidDecaySeminorm(k+6) f * (1+a)^{-4} / (1+b)^4
  -- = C_R * Z * |s_R| * (max_{k∈s_R} rapidDecaySeminorm(k+6) f) * (1+a)^{-4} / (1+b)^4
  --
  -- Actually the sup is cleaner. We need (s_R.sup p)(slice_a f) ≤ Σ_{k∈s_R} p_k(slice_a f)
  -- No, the sup is already the max, so it's ≤ any single term.

  -- Let's use a simpler approach: bound everything through a single high seminorm
  -- The resolvent bound gives: rapidDecaySeminorm 4 (equiv(R(g))) ≤ C_R * (s_R.sup rds) g
  -- The sup of a finset of seminorms evaluated at g is ≤ Σ_{k∈s_R} rds_k g
  -- But each rds_k(slice_a f) ≤ Z * rds_{k+6} f * (1+a)^{-4}
  -- So (s_R.sup rds)(slice_a f) ≤ Z * (s_total.sup rds) f * (1+a)^{-4}
  -- where s_total = s_R.image (· + 6)

  set s_total := s_R.image (· + 6) with hs_total

  -- Now: for any k ∈ s_R, rds_k(slice_a f) ≤ Z * rds_{k+6} f * (1+a)^{-4}
  have h_slice_decay : ∀ (n : ℕ) (f : CylinderTestFunction L),
      (s_R.sup RapidDecaySeq.rapidDecaySeminorm) (ntpExtractSlice n f) ≤
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

  -- Main bound chain
  refine ⟨s_total, C_R * Z, by positivity, fun m f => ?_⟩
  set a := (Nat.unpair m).1
  set b := (Nat.unpair m).2
  -- massOperatorCoord m f = (equiv(R(slice_a f))).val b
  have h_eq : massOperatorCoord L mass hmass m f =
      (schwartzRapidDecayEquiv1D
        (resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
          (ntpSliceSchwartz L a f))).val b := rfl

  -- Step A: |(equiv(R(g))).val b| * (1+b)^4 ≤ rds_4(equiv(R(g)))
  set g_schwartz := resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
      (ntpSliceSchwartz L a f)
  set g_rds := schwartzRapidDecayEquiv1D g_schwartz

  have hA : |g_rds.val b| * (1 + (b : ℝ)) ^ 4 ≤
      RapidDecaySeq.rapidDecaySeminorm 4 g_rds :=
    (g_rds.rapid_decay 4).le_tsum b
      (fun n _ => mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg n 4))

  -- Step B: rds_4(equiv(R(g))) ≤ C_R * (s_R.sup rds)(slice_a f)
  -- Note: ntpSliceSchwartz L a f = equiv⁻¹(ntpExtractSlice a f)
  -- So equiv(R(ntpSliceSchwartz L a f)) = equiv(R(equiv⁻¹(ntpExtractSlice a f)))
  have hB : RapidDecaySeq.rapidDecaySeminorm 4 g_rds ≤
      C_R * (s_R.sup RapidDecaySeq.rapidDecaySeminorm) (ntpExtractSlice a f) :=
    h_resolvent a (ntpExtractSlice a f)

  -- Step C: (s_R.sup rds)(slice_a f) ≤ Z * (s_total.sup rds) f * (1+a)^{-4}
  have hC := h_slice_decay a f

  -- Combine A, B, C:
  -- |g_rds.val b| * (1+b)^4 ≤ C_R * Z * (s_total.sup rds) f * (1+a)^{-4}
  have h_combined : |g_rds.val b| * (1 + (b : ℝ)) ^ 4 ≤
      C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
      ((1 + (a : ℝ)) ^ 4)⁻¹ := by
    calc |g_rds.val b| * (1 + (b : ℝ)) ^ 4
        ≤ RapidDecaySeq.rapidDecaySeminorm 4 g_rds := hA
      _ ≤ C_R * (s_R.sup RapidDecaySeq.rapidDecaySeminorm) (ntpExtractSlice a f) := hB
      _ ≤ C_R * (Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 4)⁻¹) := by gcongr
      _ = C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
          ((1 + (a : ℝ)) ^ 4)⁻¹ := by ring

  -- So |g_rds.val b| ≤ C_R * Z * p(f) / ((1+a)^4 * (1+b)^4)
  have h_ab_decay : |massOperatorCoord L mass hmass m f| ≤
      C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
      ((1 + (a : ℝ)) ^ 4)⁻¹ * ((1 + (b : ℝ)) ^ 4)⁻¹ := by
    rw [h_eq]
    rw [show C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
        ((1 + (a : ℝ)) ^ 4)⁻¹ * ((1 + (b : ℝ)) ^ 4)⁻¹ =
        C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
        ((1 + (a : ℝ)) ^ 4)⁻¹ / (1 + (b : ℝ)) ^ 4 from by
      rw [div_eq_mul_inv]]
    rw [le_div_iff₀ (by positivity)]
    exact h_combined

  -- Step D: use pair_decay_bound_pow to get (1+m)^{-2} decay
  -- (1+m)^2 ≤ (1+a)^4 * (1+b)^4, so 1/((1+a)^4*(1+b)^4) ≤ 1/(1+m)^2
  have h_pair := pair_decay_bound_pow a b
  have hm_eq : Nat.pair a b = m := Nat.pair_unpair m

  -- Convert rpow to pow form
  rw [show ((-2 : ℤ) : ℝ) = (-2 : ℝ) from by norm_cast,
      Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + (m : ℝ)),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast,
      Real.rpow_natCast]

  calc |massOperatorCoord L mass hmass m f|
      ≤ C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
        ((1 + (a : ℝ)) ^ 4)⁻¹ * ((1 + (b : ℝ)) ^ 4)⁻¹ := h_ab_decay
    _ = C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f /
        ((1 + (a : ℝ)) ^ 4 * (1 + (b : ℝ)) ^ 4) := by rw [div_eq_mul_inv, mul_inv]; ring
    _ ≤ C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f /
        (1 + (m : ℝ)) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [← hm_eq]; exact h_pair
    _ = C_R * Z * (s_total.sup RapidDecaySeq.rapidDecaySeminorm) f *
        ((1 + (m : ℝ)) ^ 2)⁻¹ := by rw [div_eq_mul_inv]

/-! ## Mass operator definition -/

/-- Helper: package the decay bound for `nuclear_ell2_embedding_from_decay`. -/
private def massOperator_ell2_embedding (mass : ℝ) (hmass : 0 < mass) :
    ∃ (j : CylinderTestFunction L →L[ℝ] ell2'),
      ∀ (f : CylinderTestFunction L) (m : ℕ),
        (j f : ℕ → ℝ) m = massOperatorCoord L mass hmass m f := by
  obtain ⟨s, C, hC, hdecay⟩ := massOperatorCoord_decay L mass hmass
  exact nuclear_ell2_embedding_from_decay
    (massOperatorCoord L mass hmass) s C hC hdecay

/-- **The cylinder mass operator** `T : CylinderTestFunction L →L[ℝ] ell2'`.

Constructed from the coordinate functionals `massOperatorCoord` via
`nuclear_ell2_embedding_from_decay`. The m-th coordinate is:
  `(T f)_m = coeff_b(R_{ω_a}(slice_a(f)))`
where `(a, b) = Nat.unpair m`, `ω_a = resolventFreq L mass a`, and
`slice_a` extracts the a-th spatial Fourier mode.

This is the GNS map for the covariance bilinear form: `⟨Tf, Tg⟩ = ⟨f, Cg⟩_{L²}`.
It decomposes by spatial Fourier mode: for mode n with dispersion relation
ω_n = `resolventFreq L mass n`, the temporal component undergoes the
Fourier multiplier `(p² + ω_n²)^{-1/2}` from `resolventMultiplierCLM`.

Used by `GaussianField.measure T` to construct the Gaussian probability
measure on `Configuration (CylinderTestFunction L)`. -/
def cylinderMassOperator (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2' :=
  (massOperator_ell2_embedding L mass hmass).choose

/-- The m-th coordinate of the mass operator is the coordinate functional.

  `(T f)_m = massOperatorCoord L mass hmass m f` -/
theorem cylinderMassOperator_coord (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (m : ℕ) :
    (cylinderMassOperator L mass hmass f : ℕ → ℝ) m =
    massOperatorCoord L mass hmass m f :=
  (massOperator_ell2_embedding L mass hmass).choose_spec f m

/-- The mass operator agrees with the coordinate functional description:
the m-th output is `coeff_b(R_{ω_a}(slice_a(f)))` where `(a,b) = Nat.unpair m`. -/
theorem cylinderMassOperator_formula (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (m : ℕ) :
    (cylinderMassOperator L mass hmass f : ℕ → ℝ) m =
    DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) (Nat.unpair m).2
      (resolventMultiplierCLM (resolventFreq_pos L mass hmass (Nat.unpair m).1)
        (ntpSliceSchwartz L (Nat.unpair m).1 f)) := by
  rw [cylinderMassOperator_coord]
  rfl

end GaussianField
