# Discharge plan: `cylinderMassOperator_range_dense`

**Target file**: `Cylinder/MassOperatorRangeDense.lean`
**Goal**: replace the axiom `cylinderMassOperator_range_dense` with a theorem.
**Estimated effort**: 1-2 active days of focused Lean work.

This document is a self-contained plan suitable for hand-off to an external
coding agent (codex) or for picking up in a fresh session.

## Inputs

### Existing API

* `Cylinder/MassOperatorConstruction.lean`
  * `cylinderMassOperator L mass hmass : CylinderTestFunction L →L[ℝ] ell2'`
    — the mass operator (`ell2' := lp (fun _ : ℕ => ℝ) 2`).
  * `cylinderMassOperator_formula` (line 663):
    `(T f) n = DM_{(unpair n).2} (R_{ω_{(unpair n).1}} (slice_{(unpair n).1} f))`.
  * `resolventFreq_pos L mass hmass a : 0 < resolventFreq L mass a`.
* `Cylinder/FourierMultiplier.lean`
  * `def resolventSymbol (ω : ℝ) (p : ℝ) : ℝ := (p ^ 2 + ω ^ 2) ^ (-(1 : ℝ) / 2)`
    (line 79).
  * `resolventSymbol_hasTemperateGrowth` (line 152) — exemplar proof for
    step 2 below.
  * `resolventSymbol_pos` (line 100).
  * `def realFourierMultiplierCLM σ (hσ : σ.HasTemperateGrowth) : 𝓢(ℝ) →L[ℝ] 𝓢(ℝ)`
    (line 216).
  * `theorem realFourierMultiplierCLM_comp` (line 392):
    `M_{σ₁} ∘ M_{σ₂} = M_{σ₁ · σ₂}` (with `hσ₂_even` hypothesis).
  * `def resolventMultiplierCLM hω := realFourierMultiplierCLM (resolventSymbol ω) ...`
    (line 682).
* `Cylinder/PositiveTime.lean`
  * `ntpSliceSchwartz L a : CylinderTestFunction L →L[ℝ] SchwartzMap ℝ ℝ`.
  * `ntpSliceSchwartz_pure` (line 229): for `g : SmoothMap_Circle L ℝ`,
    `h : SchwartzMap ℝ ℝ`,
    `ntpSliceSchwartz L a (NuclearTensorProduct.pure g h) =
     DyninMityaginSpace.coeff a g • h`.
* `Nuclear/NuclearTensorProduct.lean`
  * `NuclearTensorProduct.pure : E₁ → E₂ → NuclearTensorProduct E₁ E₂`.
* `SchwartzNuclear/HermiteNuclear.lean`
  * `instance schwartz_dyninMityaginSpace.HasBiorthogonalBasis`
    (line 54) on `SchwartzMap ℝ ℝ`.
* `SmoothCircle/Nuclear.lean` (HasBiorthogonalBasis on `SmoothMap_Circle L ℝ`,
  line 825).
* `HeatKernel/GreenInvariance.lean`
  * `smoothCircle_coeff_basis` (line 599) — biorthogonality on the smooth
    circle.
* `Nuclear/DyninMityagin.lean`
  * `class DyninMityaginSpace.HasBiorthogonalBasis` with field `coeff_basis`:
    `coeff n (basis m) = if n = m then 1 else 0` (line 76).
* Mathlib
  * `Mathlib.Analysis.Distribution.FourierMultiplier`:
    `fourierMultiplierCLM F (fun _ => c) = c • ContinuousLinearMap.id _ _`
    (constant symbol gives scalar multiple of identity).
  * `Mathlib.Analysis.Normed.Lp.lpSpace`:
    `lp.single (p : ℝ≥0∞) (i : ι) (a : E i) : lp E p` — single basis vector.
  * `lp.completeSpace_lp` etc. — completeness needed for density.

### Mathematical content

**Goal**: `DenseRange (⇑(cylinderMassOperator L mass hmass) : CylinderTestFunction L → ell2')`.

**Witness**: for each `n = Nat.pair a₀ b₀`, the test function

  `f_n := NuclearTensorProduct.pure (DyninMityaginSpace.basis a₀)
            (R_{ω_{a₀}}.symm (DyninMityaginSpace.basis b₀))`

(where `R_{ω}.symm := M_{(p²+ω²)^{1/2}}` is the inverse of the resolvent
multiplier) satisfies `T(f_n) = lp.single 2 n 1` exactly.

The standard basis `{lp.single 2 n 1 : n : ℕ}` has a finite-supported span
that's dense in `lp 2`, so `range T` is dense.

## Steps

### Step 1: Define the inverse resolvent symbol

**Where**: new section in `Cylinder/FourierMultiplier.lean`, after the
`resolventSymbol` definitions (around line 100, before
`realFourierMultiplierCLM`).

```lean
/-- The **inverse resolvent symbol** `(p² + ω²)^{+1/2}`. Pointwise inverse
of `resolventSymbol ω`. -/
def inverseResolventSymbol (ω : ℝ) (p : ℝ) : ℝ := (p ^ 2 + ω ^ 2) ^ ((1 : ℝ) / 2)

theorem inverseResolventSymbol_pos {ω : ℝ} (hω : 0 < ω) (p : ℝ) :
    0 < inverseResolventSymbol ω p := by
  unfold inverseResolventSymbol
  exact Real.rpow_pos_of_pos (by positivity) _

theorem inverseResolventSymbol_even (ω : ℝ) (p : ℝ) :
    inverseResolventSymbol ω (-p) = inverseResolventSymbol ω p := by
  unfold inverseResolventSymbol
  ring_nf

/-- The pointwise product is 1: `R_ω(p) · R_ω⁻¹(p) = 1`. -/
theorem resolventSymbol_mul_inverse (ω : ℝ) (hω : 0 < ω) (p : ℝ) :
    resolventSymbol ω p * inverseResolventSymbol ω p = 1 := by
  unfold resolventSymbol inverseResolventSymbol
  rw [← Real.rpow_add (by positivity)]
  norm_num
```

### Step 2: Temperate growth of the inverse symbol

**Adapt** `resolventSymbol_hasTemperateGrowth` (line 152). The key
difference: the outer function is `y ↦ y^{1/2}` (increasing for n=0,
decreasing derivatives for n≥1). Use polynomial bound `N := 1` instead
of `N := 0`.

```lean
theorem inverseResolventSymbol_hasTemperateGrowth (ω : ℝ) (hω : 0 < ω) :
    (inverseResolventSymbol ω).HasTemperateGrowth := by
  show ((fun y => y ^ ((1 : ℝ) / 2)) ∘ (fun p => p ^ 2 + ω ^ 2)).HasTemperateGrowth
  -- Adapt the resolventSymbol proof:
  -- - `comp'` with t = Set.Ioi (ω^2/2)
  -- - the inner function `p ↦ p² + ω²` has temperate growth (polynomial)
  -- - the outer function `y^{1/2}` on `(ω²/2, ∞)`:
  --     n = 0 case: y^{1/2} ≤ y (for y ≥ 1) — bounded by polynomial N=1
  --     n ≥ 1 case: y^{1/2 - n} for n ≥ 1 has exponent ≤ -1/2 < 0,
  --                so y^{1/2-n} ≤ (ω²/2)^{1/2-n} (decreasing on (ω²/2, ∞))
  -- Use the descPochhammer formula for derivatives of y^{1/2}.
  sorry
```

This is the LARGEST step (~50-80 lines). Mimic the existing
`resolventSymbol_hasTemperateGrowth` proof structure exactly; the
differences are the rpow-exponent (`1/2` instead of `-1/2`), the
required N (1 instead of 0), and the n=0 bound.

For the `n = 0` case specifically, prove `(p² + ω²)^{1/2} ≤ C · (1 + ‖p‖)`
for some `C`. Concretely `C := 1 + ω` works since
`(p² + ω²)^{1/2} ≤ |p| + ω ≤ (1 + ω) (1 + ‖p‖)` (sub-additivity of square
root + scaling).

### Step 3: Define the inverse multiplier

```lean
/-- The **inverse resolvent multiplier**, `R_ω⁻¹ = M_{(p²+ω²)^{1/2}}`. -/
def inverseResolventMultiplierCLM {ω : ℝ} (hω : 0 < ω) :
    SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  realFourierMultiplierCLM (inverseResolventSymbol ω)
    (inverseResolventSymbol_hasTemperateGrowth ω hω)
```

### Step 4: Multiplier composition gives identity

```lean
theorem realFourierMultiplierCLM_one :
    realFourierMultiplierCLM (fun _ => (1 : ℝ)) (Function.HasTemperateGrowth.const 1) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  -- Use Mathlib's fourierMultiplierCLM-with-constant lemma + lift-apply-project
  -- unfolding. Schematically:
  --   realFourierMultiplierCLM (·1·) = re ∘ (1 • id) ∘ ofReal = re ∘ ofReal = id.
  sorry

theorem resolventMultiplierCLM_comp_inverseResolventMultiplierCLM
    {ω : ℝ} (hω : 0 < ω) :
    (resolventMultiplierCLM hω).comp (inverseResolventMultiplierCLM hω) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  unfold resolventMultiplierCLM inverseResolventMultiplierCLM
  rw [realFourierMultiplierCLM_comp _ _ _ _ (inverseResolventSymbol_even ω)]
  -- Substitute σ₁ · σ₂ = 1 pointwise
  rw [show (fun p => resolventSymbol ω p * inverseResolventSymbol ω p) = (fun _ => (1 : ℝ))
      from funext (resolventSymbol_mul_inverse ω hω)]
  -- M_1 = id
  exact realFourierMultiplierCLM_one

theorem inverseResolventMultiplierCLM_comp_resolventMultiplierCLM
    {ω : ℝ} (hω : 0 < ω) :
    (inverseResolventMultiplierCLM hω).comp (resolventMultiplierCLM hω) =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  -- Same idea, swap order. Note: realFourierMultiplierCLM_comp requires evenness
  -- of the SECOND symbol. Use resolventSymbol_even.
  unfold resolventMultiplierCLM inverseResolventMultiplierCLM
  rw [realFourierMultiplierCLM_comp _ _ _ _ (resolventSymbol_even ω)]
  rw [show (fun p => inverseResolventSymbol ω p * resolventSymbol ω p) = (fun _ => (1 : ℝ))
      from funext (fun p => by rw [mul_comm]; exact resolventSymbol_mul_inverse ω hω p)]
  exact realFourierMultiplierCLM_one
```

### Step 5: Bundle as a `ContinuousLinearEquiv`

```lean
/-- The resolvent multiplier `R_ω` as a continuous linear equivalence on
`𝓢(ℝ)`. -/
def resolventMultiplierCLE {ω : ℝ} (hω : 0 < ω) :
    SchwartzMap ℝ ℝ ≃L[ℝ] SchwartzMap ℝ ℝ where
  toFun := resolventMultiplierCLM hω
  invFun := inverseResolventMultiplierCLM hω
  left_inv := fun f => by
    have h : inverseResolventMultiplierCLM hω (resolventMultiplierCLM hω f) =
        ((inverseResolventMultiplierCLM hω).comp (resolventMultiplierCLM hω)) f := rfl
    rw [h, inverseResolventMultiplierCLM_comp_resolventMultiplierCLM]; rfl
  right_inv := fun f => by
    have h : resolventMultiplierCLM hω (inverseResolventMultiplierCLM hω f) =
        ((resolventMultiplierCLM hω).comp (inverseResolventMultiplierCLM hω)) f := rfl
    rw [h, resolventMultiplierCLM_comp_inverseResolventMultiplierCLM]; rfl
  map_add' := (resolventMultiplierCLM hω).map_add
  map_smul' := (resolventMultiplierCLM hω).map_smul
  continuous_toFun := (resolventMultiplierCLM hω).continuous
  continuous_invFun := (inverseResolventMultiplierCLM hω).continuous
```

### Step 6: Witness construction and `T(f_n) = e_n`

**Where**: `Cylinder/MassOperatorRangeDense.lean`, replacing the axiom.

```lean
private def cylinderMassOperator_witness
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    CylinderTestFunction L :=
  NuclearTensorProduct.pure
    (DyninMityaginSpace.basis (Nat.unpair n).1 : SmoothMap_Circle L ℝ)
    ((resolventMultiplierCLE
      (resolventFreq_pos L mass hmass (Nat.unpair n).1)).symm
      (DyninMityaginSpace.basis (Nat.unpair n).2 : SchwartzMap ℝ ℝ))

private theorem cylinderMassOperator_witness_eq_basis
    (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    cylinderMassOperator L mass hmass
      (cylinderMassOperator_witness L mass hmass n) =
    lp.single 2 n (1 : ℝ) := by
  -- Show the m-th coordinate equals (lp.single 2 n 1) m for all m.
  -- Use lp.ext or `(cylinderMassOperator L mass hmass _) m = ...` formula.
  set a₀ := (Nat.unpair n).1
  set b₀ := (Nat.unpair n).2
  set f := cylinderMassOperator_witness L mass hmass n
  -- For each m, write m = Nat.pair a' b' (with a',b' = Nat.unpair m).
  -- Step 1: cylinderMassOperator_formula gives
  --   (T f).val m = DM_{b'}(R_{ω_{a'}}(slice_{a'}(f))).
  -- Step 2: slice_{a'}(pure(basis_a₀, h)) = δ_{a',a₀} • h
  --   by ntpSliceSchwartz_pure + smoothCircle_coeff_basis.
  -- Step 3: For a' = a₀: slice_{a₀}(f) = h := R_{ω_{a₀}}.symm(basis_{b₀}).
  --   Then R_{ω_{a₀}}(h) = R_{ω_{a₀}} ∘ R_{ω_{a₀}}.symm (basis_{b₀}) = basis_{b₀}.
  --   And DM_{b'}(basis_{b₀}) = δ_{b',b₀} (DyninMityaginSpace.coeff_basis on SchwartzMap).
  --   So (T f).val m = δ_{b',b₀} when a' = a₀, which is δ_{m, n} (since (a₀, b₀) ↔ n).
  -- Step 4: For a' ≠ a₀: slice_{a'}(f) = 0, so (T f).val m = 0.
  -- Combining: (T f).val m = δ_{m, n} = (lp.single 2 n 1).val m.
  apply lp.ext
  intro m
  set a' := (Nat.unpair m).1
  set b' := (Nat.unpair m).2
  -- ...detailed case analysis on a' = a₀ or not, and b' = b₀ or not
  sorry
```

This is the second-largest step (~80-150 lines). Most of the bookkeeping
is unfolding `cylinderMassOperator_formula`, `ntpSliceSchwartz_pure`,
biorthogonality of the bases, and the `lp.single` API.

### Step 7: Range contains the standard basis ⇒ dense

```lean
theorem cylinderMassOperator_range_dense (mass : ℝ) (hmass : 0 < mass) :
    DenseRange (⇑(cylinderMassOperator L mass hmass) : CylinderTestFunction L → ell2') := by
  -- The standard basis {lp.single 2 n 1 : n : ℕ} is in range T (witness above).
  -- Finite linear combinations of single-basis vectors are dense in lp 2.
  -- Conclusion: range T is dense.
  rw [denseRange_iff_closure_range]
  -- Or show: ∀ x ∈ ell2', x is in closure of range T.
  -- Strategy: use the lp.basis or `Finsupp.lift`-style density.
  sorry
```

The Mathlib lemma to use is something like:

* `lp.lpEquiv_finset_sum` or `lp.dense_finset_sum`,
* OR show range T is a closed subspace containing the standard basis;
* OR show closure(range T) = ⊤ via showing it contains the dense subspace
  of finite-supported sequences.

A working approach: define `S := closure (range T)`. Show:
1. `S` is a closed `Submodule ℝ ell2'`.
2. Every `lp.single 2 n 1` is in `S` (by step 6).
3. Hence every finite-support sequence is in `S` (linear combination).
4. Finite-support sequences are dense in `ell2'`
   (`Mathlib.Analysis.Normed.Lp.lpSpace`).
5. Hence `S = ⊤`, i.e., `closure (range T) = ⊤`, i.e., `DenseRange T`.

## Verification

* `lake build Cylinder` succeeds.
* `grep -nE '^axiom ' Cylinder/MassOperatorRangeDense.lean` finds nothing.
* `bash scripts/count_axioms.sh` shows total reduced from 6 to 5 in
  the `gaussian-field` directory.
* The 3 specialised `_equivariant` theorems in `Cylinder/GreenFunction.lean`
  and the master `cylinderMassOperator_equivariant` continue to compile
  unchanged.

## Notes for codex

* All API references above include line numbers as of commit `23642bb` on
  `main`. Re-grep if the file structure has shifted.
* Step 2 (temperate-growth proof) and step 6 (witness ↦ basis) are the
  two non-trivial steps. The rest is plumbing.
* For step 2, the existing `resolventSymbol_hasTemperateGrowth` proof
  (`Cylinder/FourierMultiplier.lean:152-190`) is the closest exemplar.
  Read it carefully before writing the inverse version.
* For step 6, the existing `cylinderMassOperator_formula` use sites in
  `Cylinder/MassOperatorEquivariance.lean` (e.g.,
  `cylinderMassOperator_normSq_eq_sum_perMode`) show the unfolding
  pattern.
* The `lp.single` API and `DenseRange.induction_on` (for step 7's
  closure argument) live in
  `Mathlib.Analysis.Normed.Lp.lpSpace` and
  `Mathlib.Topology.DenseEmbedding` respectively.
* If step 4 (`realFourierMultiplierCLM_one`) is annoying to prove, an
  alternative: reformulate the inverse-multiplier identity as an
  `extensionality + ext` argument over Schwartz functions (showing both
  sides agree pointwise on Fourier transforms).
* Total expected diff: ~250-400 lines added across
  `Cylinder/FourierMultiplier.lean` (steps 1-5) and
  `Cylinder/MassOperatorRangeDense.lean` (steps 6-7).

## Status after discharge

Active gaussian-field axioms: **6 → 5**. Remaining:

* `embed_l2_uniform_bound` (Cylinder/MethodOfImages.lean) — Stein-Weiss
  Poisson summation.
* `fourierMultiplier_schwartz_bound` (SchwartzFourier/ResolventUniformBound.lean)
  — Hörmander multiplier theorem on Schwartz space.
* `hermiteGalerkinTrunc_tendsto_schwartz` (SchwartzNuclear/HermiteGalerkin.lean)
  — Hermite expansion convergence in Schwartz topology.
* `hermiteFunctionNd_HO_eigenvalue` (SchwartzNuclear/HermiteGalerkin.lean)
  — multi-D HO eigenvalue equation.
* `cylinderMassOperator_spatialTranslation_norm_eq`
  (Cylinder/GreenFunction.lean) — separate ~2-3 day project via paired-mode
  rotation in `paired_coeff_product_circleTranslation`.
