/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Density Bridge: Gaussian Measure ↔ Gaussian Density

Proves that the lattice Gaussian measure (constructed via pushforward of noise)
has density `ρ(φ) = exp(-½⟨φ,Qφ⟩)` with respect to Lebesgue measure, up to
normalization.

This "density bridge" connects the abstract Gaussian field construction with
the explicit density formula needed for the FKG inequality proof.

## Main theorems

- `latticeGaussianMeasure_density_integral` — expectations under the Gaussian
  measure equal normalized weighted Lebesgue integrals
- `integrable_mul_gaussianDensity` — integrability transfer from Gaussian
  measure to Lebesgue via density

## Proof strategy

1. The pushforward `μ.map eval` (where eval maps ω to field values) has
   characteristic function `exp(-½ ⟨t, Q⁻¹t⟩)` by `GaussianField.charFun`
   and the spectral covariance identity.

2. The density measure `(1/Z)ρ · λ` has the same characteristic function,
   computed via the Gaussian Fourier transform (diagonalized by eigenbasis).

3. By `Measure.ext_of_charFun`, the two measures are equal.

4. The density bridge and integrability transfer follow.

## References

- Glimm-Jaffe, "Quantum Physics", §7.1 (Gaussian functional integrals)
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", Chapter I
-/

import Lattice.Covariance
import Lattice.SpectralCovariance

noncomputable section

namespace GaussianField

open MeasureTheory

variable (d N : ℕ) [NeZero N]

/-! ## Evaluation map -/

/-- The evaluation map from Configuration space to field values:
`eval(ω) = (fun x => ω(δ_x))`.

This extracts the field configuration from a continuous linear functional. -/
def evalMap :
    Configuration (FinLatticeField d N) → FinLatticeField d N :=
  fun ω x => ω (finLatticeDelta d N x)

/-! ## Density bridge

The core result: the lattice Gaussian measure's expectations can be computed
as normalized weighted Lebesgue integrals with the Gaussian density.

### Proof outline

**Step 1**: Characteristic function of pushforward.
By `GaussianField.charFun`:
  `E_μ[exp(i ω(f))] = exp(-½ ‖T(f)‖²_ℓ²)`
For `f = ∑ t_x δ_x`, using `spectralLatticeCovariance_norm_sq`:
  `‖T(∑ t_x δ_x)‖² = ∑_k λ_k⁻¹ |⟪e_k, t⟫|²`

**Step 2**: Characteristic function of density measure.
The Fourier transform of `ρ(φ) = exp(-½ ⟨φ, Qφ⟩)` gives, after
diagonalization in the eigenbasis:
  `∫ exp(i⟨t,φ⟩) ρ(φ) dφ = Z · exp(-½ ∑_k λ_k⁻¹ |⟪e_k, t⟫|²)`

**Step 3**: Measure uniqueness via `Measure.ext_of_charFun`.
Both measures have the same characteristic function, hence are equal.

**Step 4**: The density bridge and integrability transfer follow
from the measure equality. -/

/-- **Density bridge**: the lattice Gaussian measure equals a weighted
Lebesgue integral with the Gaussian density.

For any function F of field values, the expectation under the Gaussian measure
equals the normalized weighted integral:
`E_μ[F] = (∫ F(φ) · ρ(φ) dφ) / (∫ ρ(φ) dφ)`
where `ρ(φ) = exp(-½⟨φ, Qφ⟩)` and the integrals are against Lebesgue measure
on `FinLatticeField d N ≅ ℝ^{N^d}`.

Proof: Both measures have characteristic function `exp(-½ ⟨t, Q⁻¹t⟩)`.
The pushforward gets this from `charFun` + `spectralLatticeCovariance_norm_sq`.
The density gets this from the Gaussian Fourier transform. By
`Measure.ext_of_charFun`, the measures are equal. -/
theorem latticeGaussianMeasure_density_integral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFρi : Integrable (fun φ => F φ * gaussianDensity d N a mass φ)) :
    ∫ ω, F (fun x => ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (∫ φ, F φ * gaussianDensity d N a mass φ) /
    (∫ φ, gaussianDensity d N a mass φ) := by
  -- Step 1: Show μ.map eval = (1/Z) ρ · volume
  -- via characteristic function matching (charFun + Measure.ext_of_charFun)
  -- Step 2: Integrate F against both sides
  sorry

/-- **Integrability transfer**: for F integrable against the Gaussian measure μ,
the product F·ρ is integrable against Lebesgue measure.

This follows from the density bridge: μ has density ρ/Z with respect to
Lebesgue, so `∫|F|dμ = ∫|F|ρ/Z dλ < ∞` implies `∫|F|ρ dλ = Z · ∫|F|dμ < ∞`. -/
theorem integrable_mul_gaussianDensity (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hF : Integrable (fun ω => F (fun x => ω (finLatticeDelta d N x)))
           (latticeGaussianMeasure d N a mass ha hmass)) :
    Integrable (fun φ => F φ * gaussianDensity d N a mass φ) := by
  -- From density bridge: μ has density ρ/Z w.r.t. Lebesgue
  -- Integrability w.r.t. μ implies integrability of F·ρ w.r.t. Lebesgue
  sorry

end GaussianField
