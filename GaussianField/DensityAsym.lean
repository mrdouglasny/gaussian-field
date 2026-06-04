/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/
import Lattice.AsymCovariance
import Lattice.AsymFiniteField
import GaussianField.Density

/-!
# Asymmetric-lattice Gaussian density bridge

The heterogeneous (`Nt ≠ Ns`) analogue of `GaussianField/Density.lean`: the abstractly
constructed free Gaussian field `GaussianField.measure (latticeCovarianceAsymGJ …)` on the
configuration (weak-dual) space, pushed to coordinates by the evaluation map `evalMapAsym`,
equals the explicit Lebesgue-density Gaussian `normalizedQuadraticGaussianMeasure` with
precision `a² • massOperatorAsym` (the `d = 2` cell-area normalisation; the covariance is
supplied to `GaussianField.measure` as the *square-root* operator `a⁻¹ Q^{−1/2}`, so the
precision is `a²·Q`).

## Main definitions / theorems

* `evalMapAsym` / `evalMapAsymMeasurableEquiv` — the weak-dual ↔ coordinate measurable equiv.
* `latticeGaussianFieldLawAsym` — the free GFF pushed to coordinates.
* `latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure` — the bridge (WIP).

This is the GaussianField-side input to the Layer-B2 measure↔operator bridge in `pphi2`
(crux-1); see `docs/generic-density-bridge-plan.md` for the eventual generic consolidation.
-/

open MeasureTheory
open scoped BigOperators

namespace GaussianField

variable (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]

/-! ## `evalMapAsym` — weak-dual ↔ coordinate equivalence -/

/-- Evaluation map from configuration space to field values: `eval(ω) = (x ↦ ω(δ_x))`. -/
noncomputable def evalMapAsym : Configuration (AsymLatticeField Nt Ns) → AsymLatticeField Nt Ns :=
  fun ω x => ω (asymLatticeDelta Nt Ns x)

theorem measurable_evalMapAsym : Measurable (evalMapAsym Nt Ns) := by
  rw [measurable_pi_iff]
  intro x
  simpa [evalMapAsym] using
    (configuration_eval_measurable (E := AsymLatticeField Nt Ns) (asymLatticeDelta Nt Ns x))

/-- Basis decomposition: `φ = ∑ y, φ(y) • δ_y`. -/
theorem asym_field_basis_decomp_density (φ : AsymLatticeField Nt Ns) :
    φ = ∑ y : AsymLatticeSites Nt Ns, φ y • asymLatticeDelta Nt Ns y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, asymLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Pairing with a configuration in site coordinates. -/
theorem config_apply_eq_sum_deltaAsym (ω : Configuration (AsymLatticeField Nt Ns))
    (f : AsymLatticeField Nt Ns) :
    ω f = ∑ x : AsymLatticeSites Nt Ns, f x * ω (asymLatticeDelta Nt Ns x) := by
  conv_lhs => rw [asym_field_basis_decomp_density Nt Ns f]
  simp [map_sum, map_smul, smul_eq_mul]

theorem config_apply_eq_sum_evalMapAsym (ω : Configuration (AsymLatticeField Nt Ns))
    (f : AsymLatticeField Nt Ns) :
    ω f = ∑ x : AsymLatticeSites Nt Ns, f x * (evalMapAsym Nt Ns ω) x := by
  simpa [evalMapAsym] using config_apply_eq_sum_deltaAsym Nt Ns ω f

/-- Inverse of `evalMapAsym`: `φ ↦ (f ↦ ∑ x, f(x)·φ(x))`. -/
noncomputable def evalMapAsymInv (φ : AsymLatticeField Nt Ns) :
    Configuration (AsymLatticeField Nt Ns) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => ∑ x : AsymLatticeSites Nt Ns, f x * φ x
      map_add' := fun f g => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun c f => by
        simp only [Finset.mul_sum, smul_eq_mul, RingHom.id_apply, Pi.smul_apply]
        congr 1; ext x; ring }

theorem evalMapAsymInv_apply (φ f : AsymLatticeField Nt Ns) :
    (evalMapAsymInv Nt Ns φ) f = ∑ x : AsymLatticeSites Nt Ns, f x * φ x := by
  simp only [evalMapAsymInv]; rfl

theorem evalMap_evalMapInvAsym (φ : AsymLatticeField Nt Ns) :
    evalMapAsym Nt Ns (evalMapAsymInv Nt Ns φ) = φ := by
  ext x; simp only [evalMapAsym, evalMapAsymInv_apply, asymLatticeDelta]
  simp [Finset.mem_univ]

theorem evalMapInv_evalMapAsym (ω : Configuration (AsymLatticeField Nt Ns)) :
    evalMapAsymInv Nt Ns (evalMapAsym Nt Ns ω) = ω := by
  apply ContinuousLinearMap.ext; intro f
  exact (config_apply_eq_sum_evalMapAsym Nt Ns ω f).symm

theorem evalMapAsymInv_measurable : Measurable (evalMapAsymInv Nt Ns) := by
  apply configuration_measurable_of_eval_measurable (evalMapAsymInv Nt Ns)
  intro f; simp_rw [evalMapAsymInv_apply]
  exact Finset.measurable_sum _ (fun x _ => measurable_const.mul (measurable_pi_apply x))

/-- `evalMapAsym` as a measurable equivalence between the configuration space and the
coordinate field space. -/
noncomputable def evalMapAsymMeasurableEquiv :
    Configuration (AsymLatticeField Nt Ns) ≃ᵐ AsymLatticeField Nt Ns where
  toEquiv :=
    { toFun := evalMapAsym Nt Ns
      invFun := evalMapAsymInv Nt Ns
      left_inv := evalMapInv_evalMapAsym Nt Ns
      right_inv := evalMap_evalMapInvAsym Nt Ns }
  measurable_toFun := measurable_evalMapAsym Nt Ns
  measurable_invFun := evalMapAsymInv_measurable Nt Ns

/-! ## The field law and the density bridge -/

/-- The asym lattice field law: the free GFF (built abstractly from `latticeCovarianceAsymGJ`)
pushed to coordinates by `evalMapAsym`. -/
noncomputable def latticeGaussianFieldLawAsym (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (AsymLatticeField Nt Ns) :=
  (GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map (evalMapAsym Nt Ns)

/-- **The asym density bridge (crux-1).** The free GFF, in coordinates, is the explicit
Lebesgue-density Gaussian with precision `a² • massOperatorAsym`.

WIP: the characteristic-functional (`charFunDual`) match, reusing the existing asym DFT/spectral
lemmas (`dft_parseval_2d_asym`, `covariance_spectralLatticeCovarianceAsym_eq`,
`abstract_spectral_eq_dft_spectral_2d_asym`) through the `Density.lean` proof skeleton. -/
theorem latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    latticeGaussianFieldLawAsym Nt Ns a mass ha hmass =
      normalizedQuadraticGaussianMeasure (a ^ 2 • massOperatorAsym Nt Ns a mass) := by
  sorry

end GaussianField
