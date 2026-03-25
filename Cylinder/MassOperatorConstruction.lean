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

This combines three decay estimates:
1. `coeff_decay` for SchwartzMap: `|coeff_b(g)| * (1+b)^k ≤ C₁ * q(g)`
2. CLM continuity of resolvent: `q(R_ω(h)) ≤ C₂ * r(h)`
3. CLM continuity of slice: `r(slice_a(f)) ≤ C₃ * p(f)` (uniform in a)

Together: `|φ_m(f)| ≤ C * p(f) * (1+b)^{-k}` for any k.
Since `b ≤ m = Nat.pair a b`, we get `(1+b)^{-k} ≤ (1+m)^{-k}` as
`1+b ≤ 1+m` from `Nat.right_le_pair`. -/

/-- The mass operator coordinate functionals satisfy the nuclear decay bound
required by `nuclear_ell2_embedding_from_decay`.

For each `m` with `(a,b) = Nat.unpair m`:
  `|φ_m(f)| ≤ C · p(f) · (1+m)^{-2}`

This follows from:
- Rapid decay of Hermite coefficients: `|coeff_b(g)| ≤ C₁ · q(g) / (1+b)^4`
- Continuity of resolvent multiplier: `q(R_{ω_a}(h)) ≤ C₂ · r(h)`
- Continuity of slice extraction: `r(slice_a(f)) ≤ p(f)` (since slice is a sub-sum)
- Monotonicity: `(1+b)^{-4} ≤ (1+m)^{-2}` since `b ≤ m` and `m ≥ b²/2`. -/
theorem massOperatorCoord_decay (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (DyninMityaginSpace.ι (E := CylinderTestFunction L))) (C : ℝ) (_ : 0 < C),
    ∀ (m : ℕ) (f : CylinderTestFunction L),
      |massOperatorCoord L mass hmass m f| ≤
      (C * (s.sup DyninMityaginSpace.p) f) * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
  sorry

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
