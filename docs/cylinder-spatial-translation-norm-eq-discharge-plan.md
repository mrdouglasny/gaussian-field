# Discharge plan: `cylinderMassOperator_spatialTranslation_norm_eq`

**Target file**: `Cylinder/GreenFunction.lean` (lines 333-338, the spatial-translation
instance axiom).
**Goal**: replace the axiom with a theorem.
**Estimated effort**: 2-3 active days of focused Lean work.

This document is a self-contained plan suitable for hand-off to an external
coding agent (codex) or for picking up in a fresh session.

## Why this discharge is "routine"

All the mathematical content already exists in the repo. This is bookkeeping
across a few existing abstractions plus one new slice-rotation lemma.

The two _norm_eq instance axioms for time reflection and time translation
(both `id ⊗ S₂` for some temporal Schwartz operator `S₂`) were discharged
earlier via the parametric lemma `cylinderMassOperator_norm_eq_of_temporal_action`
in `Cylinder/MassOperatorEquivariance.lean`. That template **does not transfer**
to spatial translation because:

* Spatial translation is `S₁ ⊗ id` with `S₁ = circleTranslation L v` —
  acts on the spatial circle factor, identity on temporal.
* `slice_a((S₁ ⊗ id) f)` is **not** simply `S₁(slice_a f)`. Instead, the
  circle translation **mixes** the paired (cos_k, sin_k) Hermite-like
  modes within each frequency `k`.
* Per-mode invariance fails; only **per-pair** invariance holds.

## Existing infrastructure to reuse

### From `SmoothCircle/FourierTranslation.lean`

Public:

* `theorem paired_coeff_product_circleTranslation (k : ℕ) (hk : 0 < k) (v : ℝ) (f g : SmoothMap_Circle L ℝ)`
  (line 377) — paired-coeff product invariance on cos/sin pairs `(2k-1, 2k)`.
* `theorem fourierCoeffReal_circleTranslation_zero` (line 152) — the
  constant mode `n = 0` is translation-invariant.
* `theorem fourierCoeffReal_circleTranslation_cos`, `_sin` — explicit
  cos/sin paired-mode formulas under translation.

### From `HeatKernel/GreenInvariance.lean`

Currently **private** (would need to be made public, or reproved in the
target file). All available as templates:

* `def modePartner : ℕ → ℕ` — involution: `0 ↦ 0`, `2k-1 ↔ 2k` for `k ≥ 1`.
* `theorem modePartner_involutive` (line 247) — `modePartner ∘ modePartner = id`.
* `def modePartnerEquiv : ℕ ≃ ℕ` (line 248) — the involution as an equiv.
* `theorem modePartner_cos`, `modePartner_sin` (lines 252, 257).
* `theorem tsum_eq_of_paired_involution {σ : ℕ ≃ ℕ}` (line 263) —
  if `f` and `g` agree on `f n + f (σ n) = g n + g (σ n)`, then their tsums
  agree. **Crucial reusable lemma.**
* `theorem coeff_product_paired_translation` (line 285) — generalises
  `paired_coeff_product_circleTranslation` to all `n` (including `n = 0`)
  via `modePartner`.
* `theorem coeff_eq_fourierCoeffReal` (line 56) — bridge between
  `DyninMityaginSpace.coeff` and `fourierCoeffReal` on `SmoothMap_Circle L ℝ`.

### From `SmoothCircle/HeatEquivariance.lean`

Public:

* `theorem fourierFreq_paired (k : ℕ) (hk : 0 < k)` (line 49) —
  `fourierFreq (2k-1) = fourierFreq (2k)`.

### From `Cylinder/MassOperatorEquivariance.lean`

Currently **private** (would need to be made public, or reproved):

* `private def perModeL2SqNorm (mass : ℝ) (hmass : 0 < mass) (a : ℕ) (f) : ℝ`
  (line 122) — `∫ (R_{ω_a}(slice_a f))² dt`.
* `private theorem cylinderMassOperator_normSq_eq_sum_perMode` (line 152) —
  `‖T f‖² = ∑'_a perModeL2SqNorm a f`.

### From `Cylinder/MassOperatorConstruction.lean`

Public:

* `theorem cylinderMassOperator_formula` (line 663).
* `def resolventFreq (mass : ℝ) (n : ℕ) : ℝ := √((2πk/L)² + m²)` (line 63),
  with `k := SmoothMap_Circle.fourierFreq n`.

### From `Cylinder/PositiveTime.lean`

Public:

* `theorem ntpSliceSchwartz_pure (a : ℕ) (g : SmoothMap_Circle L ℝ) (h : SchwartzMap ℝ ℝ)`:
  `ntpSliceSchwartz L a (NuclearTensorProduct.pure g h) = DyninMityaginSpace.coeff a g • h`.

### From `Nuclear/NuclearTensorProduct.lean`

Public:

* `theorem nuclearTensorProduct_mapCLM_pure`.

## Mathematical strategy

### Step 1: `resolventFreq` is paired

```lean
theorem resolventFreq_modePartner (mass : ℝ) (n : ℕ) :
    resolventFreq L mass n = resolventFreq L mass (modePartner n)
```

For `n = 0`: `modePartner 0 = 0`, trivial.
For `n = 2k-1` or `n = 2k` (`k ≥ 1`): use `fourierFreq_paired` and unfold
`resolventFreq`.

### Step 2: Slice rotation lemma

The key new lemma. For `n : ℕ`, `v : ℝ`, `f : CylinderTestFunction L`:

```lean
theorem ntpSliceSchwartz_spatialTranslation_paired
    (n : ℕ) (v : ℝ) (f : CylinderTestFunction L) :
    -- Pair-of-squared-L²-norms invariance per spatial pair
    ∫ t, (resolventMultiplierCLM (resolventFreq_pos L mass hmass n)
            (ntpSliceSchwartz L n (cylinderSpatialTranslation L v f))) t ^ 2
    + ∫ t, (resolventMultiplierCLM (resolventFreq_pos L mass hmass (modePartner n))
            (ntpSliceSchwartz L (modePartner n) (cylinderSpatialTranslation L v f))) t ^ 2
    =
    ∫ t, (resolventMultiplierCLM (resolventFreq_pos L mass hmass n)
            (ntpSliceSchwartz L n f)) t ^ 2
    + ∫ t, (resolventMultiplierCLM (resolventFreq_pos L mass hmass (modePartner n))
            (ntpSliceSchwartz L (modePartner n) f)) t ^ 2
```

Equivalently, in `perModeL2SqNorm` form:

```lean
perModeL2SqNorm n (T_v f) + perModeL2SqNorm (modePartner n) (T_v f)
  = perModeL2SqNorm n f + perModeL2SqNorm (modePartner n) f
```

#### How to prove Step 2

Two routes:

**Route A (algebraic, via paired-coeff product, more direct)**:

1. Reduce per-mode L²-norm² to a tsum of squared DM coefficients of the
   resolvent output, via the diagonal `dm_parseval`:
   ```
   perModeL2SqNorm a f = ∑'_b (DyninMityaginSpace.coeff b
     (resolventMultiplierCLM (resolventFreq_pos L mass hmass a)
        (ntpSliceSchwartz L a f)))^2
   ```

2. Show `slice_a((T_v ⊗ id) f) = ∑'_a' coeff_a(T_v basis_{a'}) · slice_{a'}(f)`.
   By orthogonality of `T_v basis_a'` to non-paired modes, the sum
   collapses to `coeff_a(T_v basis_a) · slice_a(f) + coeff_a(T_v basis_{modePartner a}) · slice_{modePartner a}(f)`.

3. Apply `R_ω` (linear) and `DM_b` (linear).

4. Square and sum over the pair `(a, modePartner a)`. The cross terms
   cancel via `cos² + sin² = 1` (the same identity used in
   `paired_coeff_product_circleTranslation`).

**Route B (via existing `coeff_product_paired_translation`)**:

1. `coeff_product_paired_translation` gives the paired-product invariance
   for spatial Fourier coefficients: 
   ```
   ∀ g h, [coeff_n(T_v g) · coeff_n(T_v h)] + [coeff_{σ n}(T_v g) · coeff_{σ n}(T_v h)]
        = [coeff_n(g) · coeff_n(h)] + [coeff_{σ n}(g) · coeff_{σ n}(h)]
   ```
   where `σ := modePartner`.

2. Specialise `g = h` to get `[coeff_n(T_v g)]² + [coeff_{σ n}(T_v g)]²
                            = [coeff_n(g)]² + [coeff_{σ n}(g)]²`.

3. Lift to per-mode L²-norm by summing over the temporal `b` index inside.

Route A is more direct but more bookkeeping. Route B reuses the existing
`coeff_product_paired_translation` more cleanly. **Recommend Route B.**

### Step 3: Apply paired-tsum lemma

Using `tsum_eq_of_paired_involution` with `σ := modePartnerEquiv`:

```lean
∑'_a perModeL2SqNorm a (T_v f) = ∑'_a perModeL2SqNorm a f
```

once we have:
- Summability of both sides (from `cylinderMassOperator_normSq_eq_sum_perMode`).
- Pair-invariance from Step 2.

### Step 4: Conclude via squared norm

```lean
theorem cylinderMassOperator_spatialTranslation_norm_eq_proved ... :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
    ‖cylinderMassOperator L mass hmass f‖
```

By Step 3 + `cylinderMassOperator_normSq_eq_sum_perMode`, the squared norms
are equal. Take square roots (both nonneg) — same trick as in
`cylinderMassOperator_norm_eq_of_temporal_action`.

## Concrete file plan

Create new file `Cylinder/MassOperatorSpatialEquivariance.lean` (parallel
to `MassOperatorEquivariance`):

```
import Cylinder.MassOperatorEquivariance       -- for cylinderMassOperator_normSq_eq_sum_perMode + perModeL2SqNorm
import HeatKernel.GreenInvariance              -- for modePartner, tsum_eq_of_paired_involution, coeff_product_paired_translation
import SmoothCircle.HeatEquivariance           -- for fourierFreq_paired
```

### Pre-step: make private declarations public

The discharge needs these currently-private declarations to be visible:

* `Cylinder/MassOperatorEquivariance.lean`:
  - `perModeL2SqNorm` (private def, line 122)
  - `cylinderMassOperator_normSq_eq_sum_perMode` (private theorem, line 152)
* `HeatKernel/GreenInvariance.lean`:
  - `modePartner`, `modePartnerEquiv`, `modePartner_*`, `coeff_product_paired_translation`,
    `coeff_eq_fourierCoeffReal`, `tsum_eq_of_paired_involution`

**Action**: drop the `private` keywords. These are mechanical 1-line edits each.
Verify nothing breaks downstream by `lake build` after each removal.

### Step 1: `resolventFreq_modePartner`

```lean
theorem resolventFreq_modePartner (mass : ℝ) (n : ℕ) :
    resolventFreq L mass n = resolventFreq L mass (modePartner n) := by
  unfold resolventFreq
  -- Want: fourierFreq n = fourierFreq (modePartner n)
  -- Case n = 0: modePartner 0 = 0, trivial.
  -- Case n = 2k-1: modePartner = 2k. Apply fourierFreq_paired.
  -- Case n = 2k:   modePartner = 2k-1. Apply (fourierFreq_paired k hk).symm.
  congr 2
  match n with
  | 0 => simp [modePartner]
  | n + 1 =>
    rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n+1 = 2(j+1)-1 (cos)
      have hn : n + 1 = 2 * (j + 1) - 1 := by omega
      have hp : modePartner (n + 1) = 2 * (j + 1) := by
        rw [hn]; exact modePartner_cos (j + 1) (by omega)
      rw [hp, hn]; exact fourierFreq_paired (j + 1) (by omega)
    · -- n+1 = 2(j+1) (sin)
      have hn : n + 1 = 2 * (j + 1) := by omega
      have hp : modePartner (n + 1) = 2 * (j + 1) - 1 := by
        rw [hn]; exact modePartner_sin (j + 1) (by omega)
      rw [hp, hn]; exact (fourierFreq_paired (j + 1) (by omega)).symm
```

### Step 2: Per-pair L²-norm² invariance

```lean
private theorem perModeL2SqNorm_paired_translation
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f : CylinderTestFunction L) (n : ℕ) :
    perModeL2SqNorm L mass hmass n (cylinderSpatialTranslation L v f)
      + perModeL2SqNorm L mass hmass (modePartner n) (cylinderSpatialTranslation L v f)
    = perModeL2SqNorm L mass hmass n f
      + perModeL2SqNorm L mass hmass (modePartner n) f := by
  -- Outline (Route B):
  -- 1. Use `dm_parseval` (diagonal) to convert each ∫(...)² to ∑'_b (DM_b)²:
  --      perModeL2SqNorm a f = ∑'_b (DM_b(R_{ω_a}(slice_a f)))²
  -- 2. The DM_b on a SchwartzMap inherits via slice → DM_b(slice_a f) = ?
  --    ACTUALLY: ∑'_b (DM_b(R_{ω_a}(slice_a f)))² = ∫ (R_{ω_a}(slice_a f))²
  --    by dm_parseval applied diagonally (set f = g = R_{ω_a}(slice_a f)).
  -- 3. Now the question is: ∫ (R_{ω_a}(slice_a (T_v f)))²
  --                            + ∫ (R_{ω_a'}(slice_{a'} (T_v f)))²
  --                       = ∫ (R_{ω_a}(slice_a f))²
  --                            + ∫ (R_{ω_a'}(slice_{a'} f))²
  --   where a' := modePartner n.
  -- 4. Use `resolventFreq_modePartner` to identify ω_a = ω_{a'}. Call it ω.
  -- 5. Reduce to: ∫ (R_ω(slice_n(T_v f)))² + ∫ (R_ω(slice_{σ n}(T_v f)))²
  --             = ∫ (R_ω(slice_n f))² + ∫ (R_ω(slice_{σ n} f))²
  -- 6. The slices `slice_n(T_v f)` and `slice_{σ n}(T_v f)` are linear
  --    combinations of `slice_n f` and `slice_{σ n} f`:
  --      slice_n(T_v f) = α · slice_n(f) + β · slice_{σ n}(f)
  --      slice_{σ n}(T_v f) = γ · slice_n(f) + δ · slice_{σ n}(f)
  --    where (α, β, γ, δ) = rotation matrix per the
  --    paired_coeff_product_circleTranslation algebra
  --    (cos θ, ±sin θ for θ = 2π k v / L).
  -- 7. Expand the L² inner products, apply cos²θ + sin²θ = 1 and the
  --    cross-term cancellation. Result: pair sum invariant.
  --
  -- Step 6 needs an auxiliary lemma. Possible formulation:
  --
  --   theorem ntpSliceSchwartz_spatialTranslation_pair_decomp ...
  --
  -- which states the explicit linear combination using
  --   `fourierCoeffReal_circleTranslation_cos / _sin` and
  --   `fourierCoeffReal_circleTranslation_zero`.
  --
  -- Implementation note: Steps 6-7 are the bulk of the work (~100-150 lines).
  sorry
```

The slice decomposition (Step 6) is the genuinely new lemma. Its proof
follows the same DM-basis HasSum pattern used in
`ntpSliceSchwartz_tensorMap_id_left` (`Cylinder/MassOperatorEquivariance.lean:53`),
but with the `id ⊗ S₂` replaced by `circleTranslation L v ⊗ id`, and the
slice formula uses the cos/sin paired-coefficient identity instead of just
extracting the temporal factor.

### Step 3: Apply the paired-tsum lemma

```lean
theorem cylinderMassOperator_spatialTranslation_normSq_eq
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ ^ 2 =
    ‖cylinderMassOperator L mass hmass f‖ ^ 2 := by
  rw [cylinderMassOperator_normSq_eq_sum_perMode,
      cylinderMassOperator_normSq_eq_sum_perMode]
  -- Apply tsum_eq_of_paired_involution with σ = modePartnerEquiv
  apply tsum_eq_of_paired_involution
  · exact (cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)).property.summable_sq
       -- or some variant: summability of perModeL2SqNorm via its closed form (norm² < ∞).
       sorry
  · exact ... -- summability for f
       sorry
  · intro n; exact perModeL2SqNorm_paired_translation L mass hmass v f n
```

(Summability arguments may need a small auxiliary lemma — establish
that `∑'_a perModeL2SqNorm a f` converges to `‖T f‖²`, which is finite.)

### Step 4: Conclude

```lean
theorem cylinderMassOperator_spatialTranslation_norm_eq_proved
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ := by
  -- Use cylinderMassOperator_spatialTranslation_normSq_eq + sqrt + nonneg
  have h_sq := cylinderMassOperator_spatialTranslation_normSq_eq L mass hmass v f
  have hx : (0 : ℝ) ≤ ‖cylinderMassOperator L mass hmass
      (cylinderSpatialTranslation L v f)‖ := norm_nonneg _
  have hy : (0 : ℝ) ≤ ‖cylinderMassOperator L mass hmass f‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖cylinderMassOperator L mass hmass
    (cylinderSpatialTranslation L v f)‖
    - ‖cylinderMassOperator L mass hmass f‖), h_sq]
```

Same pattern as `cylinderMassOperator_norm_eq_of_temporal_action` (in
`Cylinder/MassOperatorEquivariance.lean`).

### Step 5: Replace the axiom in `Cylinder/GreenFunction.lean`

Currently (lines 333-338):

```lean
axiom cylinderMassOperator_spatialTranslation_norm_eq
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
    ‖cylinderMassOperator L mass hmass f‖
```

Replace with:

```lean
theorem cylinderMassOperator_spatialTranslation_norm_eq
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ :=
  cylinderMassOperator_spatialTranslation_norm_eq_proved L mass hmass v f
```

`Cylinder/GreenFunction.lean` will need a new import:

```lean
import Cylinder.MassOperatorSpatialEquivariance
```

The `cylinderSpatialTranslationSym.preserves_T_norm` and `_inv` fields
will continue to compile unchanged (they delegate to this theorem +
the same theorem applied at `(-v)`).

## Acceptance criteria

* `lake build Cylinder` succeeds.
* `grep -nE '^axiom cylinderMassOperator_spatialTranslation' Cylinder/GreenFunction.lean`
  returns nothing.
* The `cylinderSpatialTranslationSym` constructor (lines 358-365 of
  `Cylinder/GreenFunction.lean`) continues to type-check without changes.
* The downstream theorems `cylinderMassOperator_spatialTranslation_equivariant`
  (line ~448) and `cylinderGreen_spatialTranslation_invariant` (line ~488)
  continue to compile.
* `bash scripts/count_axioms.sh` shows axiom count reduced (5 → 4 in
  the active build).

## Notes for codex

* Check whether the `private` declarations in `MassOperatorEquivariance.lean`
  and `HeatKernel/GreenInvariance.lean` need to remain private for any
  reason. The cleanest path is to make them public and reuse them. If not
  desired, reproduce the lemmas inline (~50 LOC of mechanical duplication).
* Step 2 (`perModeL2SqNorm_paired_translation`) is the genuinely new
  content (~100-150 lines). The cross-term cancellation when expanding
  `‖α v + β w‖² + ‖γ v + δ w‖²` should reduce to `α² + γ² = 1`,
  `β² + δ² = 1`, `αβ + γδ = 0` via `Real.sin_sq_add_cos_sq`, by analogy with
  the closing `linear_combination` in
  `paired_coeff_product_circleTranslation`.
* Summability inputs at Step 3 may need auxiliary lemmas — easiest is to
  prove `Summable (fun a => perModeL2SqNorm L mass hmass a f)` from
  `cylinderMassOperator_normSq_eq_sum_perMode` (the LHS is `‖T f‖²` which
  is finite, so the sum converges).
* The `nlinarith [...]` square-root extraction at Step 4 is identical to
  the existing pattern in `cylinderMassOperator_norm_eq_of_temporal_action`
  (line 187 of `MassOperatorEquivariance.lean`). Copy verbatim.
* If the slice-decomposition lemma (the inner working of Step 2) becomes
  too unwieldy, an alternative is to prove the per-pair invariance for
  pure tensors first (using `nuclearTensorProduct_mapCLM_pure` +
  `ntpSliceSchwartz_pure` + `paired_coeff_product_circleTranslation`),
  then extend to general `f` via the `DyninMityaginSpace.hasSum_basis`
  Schauder-basis pattern (same pattern used in
  `ntpSliceSchwartz_tensorMap_id_left`).
* Total expected diff: ~200-300 lines added across
  `Cylinder/MassOperatorSpatialEquivariance.lean` (new file),
  ~5-10 lines in `Cylinder/GreenFunction.lean` (axiom → theorem replacement
  + import), and ~6 `private` removals across two existing files.

## Status after discharge

Active gaussian-field axioms: **5 → 4**.

Remaining 4 are all "deep textbook" axioms standing on substantial
classical analysis:

1. `embed_l2_uniform_bound` (Stein-Weiss Poisson summation +
   uniform Riemann-sum control).
2. `fourierMultiplier_schwartz_bound` (Hörmander multiplier on Schwartz).
3. `hermiteGalerkinTrunc_tendsto_schwartz` (Hermite expansion convergence
   in Schwartz topology).
4. `hermiteFunctionNd_HO_eigenvalue` (multi-D HO eigenvalue equation
   via separation of variables).

These are all genuinely "deep" — discharging them is a separate
longer-term project.
