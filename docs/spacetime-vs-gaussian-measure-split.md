# Future split: spacetime vs Gaussian measure

Planning doc — *no immediate PR*. Sketches a future refactor that splits
`gaussian-field` into two lake packages along its natural orthogonal axis.

## Motivation

`gaussian-field` currently carries two largely independent concerns:

1. **Spacetime infrastructure** — the analytic-topological data of the
   test-function spaces and the geometry on which fields live. Lattice
   Laplacian / DFT, Schwartz-nuclear machinery, smooth functions on
   `S¹`, cylinder algebra, heat kernel, mass operator, torus, Sobolev,
   continuum-limit scaffolding. **No probability content.**
2. **Gaussian-measure theory** — abstract Gaussian measures on those
   spaces, characteristic functionals, Wick / Hermite chaos
   decomposition, hypercontractivity, density formulas, polynomial
   density in `L²(μ)`.

Track 2 (DFT machinery moved from pphi2 → gaussian-field) made the
boundary visible. The continuum-limit work that's coming next reinforces
it: continuum-limit *scaffolding* (test-function densities, Schwartz
seminorm bounds, weak-convergence statements) is purely
analytic-topological and belongs on the spacetime side; specific
*Gaussian* covariance convergence is a downstream consumer.

## Chosen boundary

**Spacetime vs Gaussian measure** (decided 2026-05-09).

An earlier sketch in pphi2 (`docs/track2-upstream-dft-machinery.md`)
proposed `lattice-spectrum` vs everything else. That cut leaves cylinder
geometry stranded in the Gaussian package and is the wrong granularity:
the natural orthogonal axis is analytic infrastructure vs probability,
not 1-d vs everything-else.

## Package A: `spacetime` (working name)

Analytic-topological infrastructure. No probability content.

```
Lattice/                  -- geometry, Laplacian, DFT, spectral covariance
SmoothCircle/             -- smooth functions on S¹, Fourier translation
SchwartzNuclear/          -- nuclear Schwartz, Hermite/Galerkin, DM coeffs
Nuclear/                  -- NuclearTensorProduct, RapidDecaySeq
SchwartzFourier/          -- Fourier multipliers, resolvent uniform bounds
Sobolev/                  -- Sobolev spaces
HeatKernel/               -- heat-kernel infrastructure
Cylinder/                 -- cylinder test functions, mass op, Green fn,
                          -- positive-time submodule, embedding to torus
Torus/                    -- torus geometry
ContinuumLimit/           -- NEW: abstract continuum-limit structure
                          -- (lattice → continuum, cylinder → torus → continuum)
```

The new `ContinuumLimit/` directory is the unifying piece: it hosts an
abstract `IsContinuumLimit` predicate over a sequence of test-function
pullbacks plus weak convergence on the dual, without committing to any
specific measure. `pphi2`'s `IsPphi2Limit` and `IsPphi2ContinuumLimit`,
and `gaussian-field`'s Gaussian-specific continuum-limit content, both
specialise it.

## Package B: `gaussian-field` (slimmed to "Gaussian measure")

Probability theory built on top of `spacetime`.

```
GaussianField/            -- IsGaussian, characteristic functional,
                             latticeGaussianMeasure, gaussianContinuumMeasure
GaussianField/Density.lean         -- density formulas
GaussianField/Hypercontractive.lean -- Nelson hypercontractivity
GaussianField/WickMultivariate.lean -- Wick ordering
GaussianField/WickHermite.lean      -- Hermite decomposition
GaussianField/StandardGaussianBridge.lean
GeneralResults/PolynomialDensityGaussian.lean
GaussianField/Continuum.lean       -- specialise spacetime ContinuumLimit
                                      to Gaussian-covariance convergence
```

Depends on `spacetime` for test-function spaces, lattice spectrum,
cylinder algebra, and the abstract continuum-limit structure.

## Boundary calls

A few files / declarations have ambiguous placement and need a deliberate
call:

- `Lattice/Covariance.lean` (`latticeCovariance`, abstract CLM) — stays
  in **spacetime** (it's a CLM, no measure content).
- `lattice_covariance_eq_spectral`, `lattice_covariance_GJ_eq_spectral`
  — stay in **spacetime** (spectral identity).
- `latticeGaussianMeasure` and the Density.lean integral identities
  — **gaussian-field** (probability content).
- Spacetime exports an `Lattice` namespace; gaussian-field reuses it for
  the lattice-Gaussian specialisations.

## Why split?

1. **Separation of concerns.** Analytic-topological infrastructure vs
   probability. Matches the actual orthogonal axis of the math.
2. **Reusability.** Sibling projects (LGT, transfer matrix, classical
   field theory, deterministic PDE) want spacetime infrastructure
   without the Gaussian-measure stack. `spacetime` becomes a useful
   standalone dependency.
3. **Smaller dependency footprint.** Mathlib's probability stack is
   heavy; downstream consumers of `spacetime` won't have to pull it in.
4. **Independent evolution.** Spacetime API is stabilising; the
   Gaussian / probability side will continue to grow as we add
   non-Gaussian (e.g. interacting) machinery.
5. **Continuum-limit unification.** Forces the abstract continuum-limit
   structure to live where it belongs (spacetime side) instead of being
   duplicated per-measure. This is the immediate forcing function: the
   cleanest place to add `ContinuumLimit/` is post-split.

## Estimate

**~2-3 weeks active, ~4-6 weeks wall-clock.** Larger than the earlier
lattice-spectrum-only sketch because cylinder, Schwartz-nuclear, torus,
and Sobolev all move with `spacetime`, and these are the bulk of the
repo. Mostly mechanical:

1. **Inventory** every file; tag spacetime vs measure (~1 day).
2. **Resolve ambiguous boundary calls** (~1 day; mostly the
   `latticeCovariance` / `lattice_covariance_GJ` placement).
3. **Carve out `spacetime`** as a new lake project; move files; update
   imports (~1 week).
4. **Slim `gaussian-field`** to depend on `spacetime` (~2 days).
5. **Introduce `ContinuumLimit/` abstraction** in `spacetime`; refactor
   any existing Gaussian-continuum-limit content to specialise it
   (~3-4 days).
6. **Update consumers**: pphi2, OSforGFF, OSreconstruction,
   brownian-motion (~2-3 days each, mostly imports).

## Status

Not started. This is post-discharge work; the immediate priority remains
the 3 `_norm_eq` axioms in `Cylinder/GreenFunction.lean` (see
`docs/gaussian-field-norm-eq-discharge-plan.md` in pphi2 — but the plan
document itself probably should also migrate here once we're committed).
