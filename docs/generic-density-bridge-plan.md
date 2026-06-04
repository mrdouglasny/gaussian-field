# Plan A — generic finite-dimensional Gaussian density bridge

**Status: proposed (not started). Consolidation refactor; do *after* the asym port (Plan B)
lands so there are two concrete instances to generalize against.**

## Goal

Replace the per-lattice density bridges (`GaussianField/Density.lean` for the square
`FinLatticeField`, and the forthcoming asym analogue from Plan B) with **one generic theorem**:
the abstractly-constructed `GaussianField.measure`, pushed to coordinates, is the explicit
Lebesgue-density Gaussian with precision = inverse covariance. Both lattices then become
one-line instantiations.

## The generic statement

For a finite-dimensional real coordinate space `E = ι → ℝ` (`ι` a `Fintype`) and a
**covariance square-root operator** `T : E →L[ℝ] H` (the object `GaussianField.measure`
consumes; recall `GaussianField.covariance T f g = ⟨T f, T g⟩`, so the genuine covariance
bilinear form is `f ↦ ‖T f‖²` and the precision is its inverse):

```
theorem gaussianMeasure_map_eval_eq_normalizedQuadraticGaussianMeasure
    (T : E →L[ℝ] H) (hT : -- nondegeneracy: the covariance form is positive-definite)
    (GaussianField.measure T).map evalMap
      = normalizedQuadraticGaussianMeasure (precisionOf T)
```

where
- `evalMap : Configuration E ≃ᵐ E`, `ω ↦ (x ↦ ω (basisDelta x))` — the generic
  WeakDual↔coordinate measurable equiv for finite-dim `E` (generalize `evalMap`/`evalMapInv`/
  `evalMapMeasurableEquiv` from `Density.lean`, which are already basis-delta-based);
- `precisionOf T : E →L[ℝ] E` is the operator whose quadratic form is the inverse of
  `f ↦ ‖T f‖²` (for the lattice instances this is `a^d • massOperator`, since
  `‖latticeCovarianceGJ f‖² = a^{-d}⟨f, (massOperator)^{-1} f⟩`);
- `normalizedQuadraticGaussianMeasure Q = (volume.withDensity exp(−½⟨φ,Qφ⟩))` normalized —
  **already generic** in `Density.lean` (`quadraticGaussianMeasure`, no lattice content).

## Why it generalizes cleanly

The square proof (`latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure`) is already
**`charFunDual`-based** (Cramér–Wold): it reduces via `MeasureTheory.Measure.ext_of_charFunDual`
to `normalizedGaussianDensityMeasure_charFunDual_eq_latticeGaussianFieldLaw`, i.e. the two
measures have equal characteristic functionals. Neither half of that is lattice-specific in
spirit:
- **abstract side** `charFunDual (GaussianField.measure T) L = exp(−½‖T L♯‖²)` — this is a
  generic `GaussianField` fact (Gaussianity of dual pairings, `pairing_is_gaussian`).
- **density side** `charFunDual (normalizedQuadraticGaussianMeasure Q) L = exp(−½⟨L♯, Q⁻¹ L♯⟩)`
  — the Fourier transform of a finite-dim Gaussian density. The square proof routes this through
  the eigenbasis of `massOperator`; the **generic** version routes it through the eigenbasis of
  `Q` (any positive-definite symmetric `Q`), using
  `integral_cexp_neg_half_sum_mul_sq_add_linear` (already generic, diagonalizes in an
  orthonormal eigenbasis).

So the only lattice-specific inputs are: (1) `precisionOf T = Q` is positive-definite symmetric;
(2) `‖T f‖² = ⟨f, Q⁻¹ f⟩`. Both are supplied per instance.

## Migration

1. Generalize `evalMap`/`evalMapInv`/`evalMapMeasurableEquiv` to any finite-dim `E = ι → ℝ`
   with the standard delta basis (the square defs are already in this shape; drop the
   `FinLatticeField`-specific names).
2. State + prove `gaussianMeasure_map_eval_eq_normalizedQuadraticGaussianMeasure` generically
   (the `charFunDual` skeleton, with `Q`'s eigenbasis in place of `massOperator`'s).
3. Re-derive the **square** `latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure` as a
   one-line instance (`T := latticeCovarianceGJ`, `Q := a^d • massOperator`, plug
   positive-definiteness `massOperator_pos_def` + `‖T f‖² = …` from `covariance_spectral…_eq`).
4. Re-derive the **asym** bridge (Plan B's `latticeGaussianFieldLawAsym_eq_…`) as the other
   instance (`T := latticeCovarianceAsymGJ`, `Q := a² • massOperatorAsym`).
5. Delete the now-redundant per-lattice charFunDual/Fourier lemmas (keep thin instance wrappers).

## Risks / cost

- The square `Density.lean` charFunDual proof is ~1000 lines and intricate; generalizing it
  (rather than re-porting) is the bulk of the work. Estimate: a focused week, mostly mechanical
  once the generic eigenbasis Fourier lemma is isolated.
- Watch the covariance **square-root** convention (`measure T` uses `T`, covariance is `‖T·‖²`);
  the precision is `(T*T)⁻¹`, not `T⁻¹`. (This is the `a^d` vs `a^{d/2}` trap — see the asym
  derivation note in `reflection-positivity`/`pphi2`.)
- Do **after** Plan B: two concrete instances (square + asym) make the right generic signature
  obvious and give regression targets. Generalizing against one instance risks over-fitting to
  `massOperator`'s specific spectral API.

## Payoff

One theorem, every finite-dim Gaussian field (square torus, asym torus, future spin lattices,
any `ι → ℝ` GFF) gets the measure↔Lebesgue-density bridge for free — the reusable core behind
every lattice φ⁴ transfer-matrix / variance argument.
