# gaussian-field TODO

**0 axioms, 0 sorries** in every library target (2026-10-22).

## Removed from `future/` (2026-10-22)

The Lean files in `future/` that declared axioms or used `sorry` were deleted
from the fork (restore from `0a53a69` with `git show 0a53a69:future/<file>`).
None was in a library target or imported by any module.

- `future/KolmogorovGaussian.lean` — opaque `axiom NuclearSpaceStd : … → Prop`
  and `axiom kolmogorov_gaussian_measure`. The Kolmogorov/Minlos route is
  proved in OSforGFF (`OSforGFF.MinlosGaussianProved`), which lgt already
  requires.
- `future/PositionKernel.lean` — `axiom mehlerKernel_eq_series` (Mehler's
  formula for the Hermite-function series). Proof target: Mehler's formula;
  the file's other results depended on it.
- `future/CylinderReflectionPositivity.lean` — one `sorry`
  (`lorentzian_convolution_pointwise`) masking 2π-convention errors in the
  stated constants (see `status.md`).

## All former axioms moved to `future/`

All axioms have been removed from the main build path and documented as
future proof targets in `future/`:

- `future/gaussian_field_axioms.lean` — `measure_unique_of_charFun`,
  `not_supported_of_not_hilbertSchmidt`, `supportHilbertSpace_exists`
- `future/configuration_torus.lean` — `configuration_torus_polish`,
  `configuration_torus_borelSpace`
- `future/mehler_kernel.lean` — `mehlerKernel_eq_series`

None are used by pphi2 or any downstream code.

---

## Completed items (for reference)

### DFT / circulant diagonalization — **DONE**
All 3 target axioms proved (Lattice/CirculantDFT.lean, CirculantDFT2d.lean).

### Green's function invariance — **DONE**
Both pure-tensor axioms proved (HeatKernel/GreenInvariance.lean).

### Bilinear extension from pure tensors — **DONE**
`greenFunctionBilinear_invariant_of_pure` proved via two-step DM expansion.

### Nuclear tensor product functor — **DONE**
All 4 axioms proved (Nuclear/TensorProductFunctorAxioms.lean):
`mapCLM`, `mapCLM_pure`, `mapCLM_id`, `mapCLM_comp`.
Also: `swapCLM`, `swapCLM_pure`.

### Measure uniqueness (finite-dimensional) — partial
`measure_unique_of_charFun` could be partially proved using finite-dimensional
Lévy if the cylinder-set infrastructure (see `future/configuration_torus.lean`)
were available. Moved to `future/gaussian_field_axioms.lean`.
