/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FKG Inequality for Lattice Gaussian Measures

States the FKG (Fortuin-Kasteleyn-Ginibre) inequality for the lattice
Gaussian measure and for measures with log-concave perturbations.

## Main axioms

- `fkg_lattice_gaussian` — E[F·G] ≥ E[F]·E[G] for monotone F, G
- `fkg_perturbed` — same for (1/Z) exp(-V) dμ₀ when V is convex

## Mathematical background

The FKG inequality is a correlation inequality: increasing (monotone)
functions of the field are positively correlated under any log-concave
measure. The Gaussian measure has density ∝ exp(-½ ⟨φ, Cφ⟩) with C
positive definite, hence log-concave.

More generally, if V is convex, then exp(-V) · exp(-½ ⟨φ,Cφ⟩) is
log-concave, so the perturbed measure dμ_V = (1/Z) exp(-V) dμ₀
also satisfies FKG. This covers P(φ)₂ with even polynomial P bounded below.

## Development path toward proof

1. Prove the FKG lattice condition for product measures (Harris-Kleitman)
2. Verify the lattice condition for Gaussian measures (log-concave density)
3. Verify preservation under convex perturbation
4. Connection to Mathlib's `IsUpperSet.le_card_inter_finset` (the {0,1}^n case)

## References

- Fortuin, Kasteleyn, Ginibre (1971), "Correlation inequalities on some
  partially ordered sets"
- Glimm-Jaffe, "Quantum Physics", §19 (Correlation inequalities)
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", §IV
-/

import Lattice.Covariance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

namespace GaussianField

open MeasureTheory

variable (d N : ℕ) [NeZero N]

/-! ## Monotonicity on Configuration space

The field configurations live in `Configuration (FinLatticeField d N)` =
`WeakDual ℝ (FinLatticeField d N)`. Since `WeakDual` does not carry a
`Preorder` instance, we define monotonicity via the pointwise order on
field evaluations at lattice sites. -/

/-- A function on configurations is *FKG-monotone* if it is increasing
with respect to pointwise ordering of field values at lattice sites:
whenever `ω₁(δ_x) ≤ ω₂(δ_x)` for all sites x, then `F(ω₁) ≤ F(ω₂)`. -/
def IsFieldMonotone (F : Configuration (FinLatticeField d N) → ℝ) : Prop :=
  ∀ ω₁ ω₂ : Configuration (FinLatticeField d N),
    (∀ x : FinLatticeSites d N, ω₁ (finLatticeDelta d N x) ≤ ω₂ (finLatticeDelta d N x)) →
    F ω₁ ≤ F ω₂

/-! ## FKG for the Gaussian measure -/

/-- **FKG inequality for the lattice Gaussian measure.**

For FKG-monotone functions F, G on Configuration space,
the Gaussian measure satisfies:
  `E_μ[F · G] ≥ E_μ[F] · E_μ[G]`

That is, increasing functions are positively correlated.

Proof outline (to be formalized):
1. The Gaussian density exp(-½ ⟨φ, Cφ⟩) is log-concave.
2. The FKG lattice condition holds for log-concave densities.
3. The lattice condition implies the correlation inequality by induction
   on the number of variables (Holley 1974). -/
axiom fkg_lattice_gaussian (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable F (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable G (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (F * G) (latticeGaussianMeasure d N a mass ha hmass)) :
    (∫ ω, F ω * G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) ≥
    (∫ ω, F ω ∂(latticeGaussianMeasure d N a mass ha hmass)) *
    (∫ ω, G ω ∂(latticeGaussianMeasure d N a mass ha hmass))

/-! ## FKG for perturbed measures -/

/-- **FKG inequality for the perturbed (interacting) measure.**

If V : Configuration → ℝ is convex, then the perturbed measure
  `dμ_V = (1/Z) exp(-V) dμ₀`
also satisfies FKG for FKG-monotone F, G.

This covers P(φ)₂ field theory where V(ω) = a^d Σ_x :P(ω(δ_x)): with P
an even polynomial bounded below.

Proof outline (to be formalized):
1. The density of μ_V w.r.t. Lebesgue is exp(-V) · exp(-½ ⟨φ,Cφ⟩),
   which is log-concave (sum of convex functions is convex).
2. Apply the general FKG theorem for log-concave measures. -/
axiom fkg_perturbed (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (V : Configuration (FinLatticeField d N) → ℝ)
    (hV_convex : ConvexOn ℝ Set.univ V)
    (hV_integrable : Integrable (fun ω => Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    -- Integrability w.r.t. the perturbed measure (stated via Gaussian measure):
    (hFi : Integrable (fun ω => F ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable (fun ω => G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (fun ω => F ω * G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass)) :
    -- E_V[F·G] · Z ≥ E_V[F] · E_V[G] / Z
    -- Stated in un-normalized form (avoids dividing by Z):
    let μ := latticeGaussianMeasure d N a mass ha hmass
    (∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ) * (∫ ω, Real.exp (-V ω) ∂μ) ≥
    (∫ ω, F ω * Real.exp (-V ω) ∂μ) * (∫ ω, G ω * Real.exp (-V ω) ∂μ)

end GaussianField
