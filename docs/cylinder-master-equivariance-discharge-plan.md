# Discharge plan: `cylinderMassOperator_equivariant`

The master equivariance axiom in `Cylinder/GreenFunction.lean` claims:

> For any `S : CylinderSpacetimeSymmetry L mass hmass`, there exists a linear
> isometric equivalence `U : ell2' ≃ₗᵢ[ℝ] ell2'` with `T(Sf) = U(Tf)` for
> all `f`, where `T = cylinderMassOperator`.

This document records the plan for replacing the axiom with a theorem.

## Inputs already available

* `cylinderMassOperator_injective` (`Cylinder/GreenFunction.lean:185`) — `T`
  is injective.
* `cylinderMassOperator_range_dense` (`Cylinder/MassOperatorRangeDense.lean`,
  axiom 2026-05-10) — range of `T` is dense in `ell2'`. Itself a special
  case of the general tensor-product mass-operator range-density theorem.
* `S.preserves_T_norm` — the structure carries `‖T(Sf)‖ = ‖Tf‖`.
* `Mathlib.Analysis.Normed.Operator.Extend.LinearEquiv.extend` — extension
  of a `LinearEquiv` to a `ContinuousLinearEquiv` along dense linear maps,
  given norm bounds.

## Mathematical sketch (Wigner-style)

1. Define `U` on `range T` via `U(Tf) := T(Sf)`. Well-defined by injectivity:
   `Tf = Tg ⇒ f = g ⇒ Sf = Sg ⇒ T(Sf) = T(Sg)`.
2. Linearity from linearity of `T` and `S`.
3. Isometry on range: `‖U(Tf)‖ = ‖T(Sf)‖ = ‖Tf‖` by `preserves_T_norm`.
4. Extend to `closure(range T) = ell2'` by uniform continuity / completeness.
5. **For `LinearIsometryEquiv` (rather than `LinearIsometry`)**: surjectivity.
   Holds when `S` is bijective (with `S⁻¹` also a Euclidean symmetry —
   automatic for translations + reflection).

## Lean strategy: use `LinearEquiv.extend`

Mathlib's `LinearEquiv.extend` (`Mathlib.Analysis.Normed.Operator.Extend`)
provides exactly the right tool, with signature:

```lean
def LinearEquiv.extend (f : E ≃ₛₗ[σ₁₂] F) (e₁ : E →ₗ[𝕜] Eₗ) (e₂ : F →ₗ[𝕜₂] Fₗ)
    (h_dense₁ : DenseRange e₁) (h_norm₁ : ∃ C, ∀ x, ‖e₂ (f x)‖ ≤ C * ‖e₁ x‖)
    (h_dense₂ : DenseRange e₂) (h_norm₂ : ∃ C, ∀ x, ‖e₁ (f.symm x)‖ ≤ C * ‖e₂ x‖) :
    Eₗ ≃SL[σ₁₂] Fₗ
```

Plug in:
* `E = F = CylinderTestFunction L`,  `Eₗ = Fₗ = ell2'`.
* `e₁ = e₂ = (cylinderMassOperator L mass hmass).toLinearMap`.
* `f = S as a LinearEquiv` (requires explicit inverse — see below).
* `h_dense₁ = h_dense₂ = cylinderMassOperator_range_dense`.
* `h_norm₁ = preserves_T_norm` reformulated as `‖T(Sf)‖ ≤ 1·‖Tf‖`.
* `h_norm₂ = preserves_T_norm_inv` (the inverse also preserves T-norm).

Result: `U : ell2' ≃SL[ℝ] ell2'` (continuous linear equivalence).

Then upgrade to `LinearIsometryEquiv` by:
1. By `LinearEquiv.extend_eq`, `U(Tf) = T(Sf)` for `f ∈ V`.
2. By `preserves_T_norm`, `‖U(Tf)‖ = ‖T(Sf)‖ = ‖Tf‖`. So `U` is an isometry on
   `range T`.
3. By density of `range T` in `ell2'` and continuity of `U` and `‖·‖`, `U` is
   an isometry on all of `ell2'`.
4. Build `LinearIsometryEquiv` from the underlying `LinearEquiv` part of
   `U` plus the `norm_map'` field.

## Required structure change: add inverse to `CylinderSpacetimeSymmetry`

To use `LinearEquiv.extend`, `S.toCLM` needs to be a `LinearEquiv`. The
cleanest way: add an explicit `inverse` field plus composition proofs to
`CylinderSpacetimeSymmetry`:

```lean
structure CylinderSpacetimeSymmetry (mass : ℝ) (hmass : 0 < mass) where
  toCLM : CylinderTestFunction L →L[ℝ] CylinderTestFunction L
  inverse : CylinderTestFunction L →L[ℝ] CylinderTestFunction L
  toCLM_comp_inverse : toCLM.comp inverse = ContinuousLinearMap.id ℝ _
  inverse_comp_toCLM : inverse.comp toCLM = ContinuousLinearMap.id ℝ _
  heat_comm : ...
  preserves_T_norm : ...
  preserves_T_norm_inv : ∀ f, ‖T (inverse f)‖ = ‖T f‖
```

The 3 instances supply explicit inverses:

* `cylinderSpatialTranslationSym v` ↔ inverse is `cylinderSpatialTranslation L (-v)`.
  Composition identity from `circleTranslation_add` + `nuclearTensorProduct_mapCLM_id`.
* `cylinderTimeTranslationSym τ` ↔ inverse is `cylinderTimeTranslation L (-τ)`.
  Composition identity from `schwartzTranslation_add` (Mathlib) + `nuclearTensorProduct_mapCLM_id`.
* `cylinderTimeReflectionSym` ↔ involutive (inverse = self).
  Composition identity from `schwartzReflection_involution`
  (`Cylinder/Symmetry.lean:78`) + `nuclearTensorProduct_mapCLM_id`.

`preserves_T_norm_inv` for each instance follows from the corresponding
`_norm_eq` theorem applied to the inverse symmetry (already proved for
time reflection and time translation; for spatial translation, follows
from the existing axiom applied to `-v`).

## Estimated work

* **Structure update + 3 Sym constructors**: ~0.5 day. The 3 composition
  identities each require `nuclearTensorProduct_mapCLM_comp` +
  `nuclearTensorProduct_mapCLM_id` + the relevant 1D involution / addition law.
* **Build `LinearEquiv` from CylinderSpacetimeSymmetry**: ~0.5 day. Bundle
  `toCLM` + `inverse` + composition proofs.
* **Apply `LinearEquiv.extend`**: ~0.5 day. Mostly plumbing; reformulating
  `preserves_T_norm` as a norm bound is straightforward (with `C := 1`).
* **Upgrade `ContinuousLinearEquiv` → `LinearIsometryEquiv`**: ~1 day. Needs
  the density-extension argument for `‖U x‖ = ‖x‖`.
* **Wire into the 3 specialised `_equivariant` theorems**: ~0.25 day.
* **Plumbing + bookkeeping**: ~0.25 day.

**Total: ~2.5–3 active days.**

## Status

* Range-density axiom: **landed** (`Cylinder/MassOperatorRangeDense.lean`,
  2026-05-10). Documented as a special case of the general theorem;
  full discharge of the axiom itself is ~1-2 days separately.
* Master discharge: **planned** (this doc). ~2.5-3 days when prioritised.
* Spatial-translation `_norm_eq` axiom: **separate ~2-3 day project** via
  paired-mode rotation argument (independent of master discharge).

## After this lands

Active gaussian-field axiom count: **6 → 4** (removes
`cylinderMassOperator_equivariant`, leaves only the three foundation axioms
`cylinderMassOperator_range_dense`, `cylinderMassOperator_spatialTranslation_norm_eq`,
plus the general unrelated 4 — `embed_l2_uniform_bound`,
`fourierMultiplier_schwartz_bound`, and the two HermiteGalerkin axioms.)

Wait — strictly: 6 axioms before this discharge become 5 after removing
`cylinderMassOperator_equivariant`. Then if `cylinderMassOperator_range_dense`
is later discharged via the general theorem (~1-2 days), 4. Then if
`cylinderMassOperator_spatialTranslation_norm_eq` is discharged (~2-3 days),
3. The remaining 3 (`embed_l2_uniform_bound`, `fourierMultiplier_schwartz_bound`,
`hermiteGalerkinTrunc_tendsto_schwartz`, `hermiteFunctionNd_HO_eigenvalue`)
total 4 axioms — these are the genuinely "deep" axioms standing on textbook
analysis (Poisson summation, Hörmander multiplier, multi-index Hermite
basis), and would be a separate longer-term discharge effort.
