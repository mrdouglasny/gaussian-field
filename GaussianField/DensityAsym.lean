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

/-! ### Asym Gaussian density and the intermediate normalized density measure

Mirrors `GaussianField/Density.lean` (`gaussianDensity`, `gaussianDensityMeasure`,
`normalizedGaussianDensityMeasure`), specialised to the heterogeneous lattice with `d = 2`. -/

/-- Asym Gaussian density `ρ(φ) = exp(-(a²/2) ⟨φ, Q φ⟩)` (Glimm–Jaffe-aligned, `d = 2`). -/
noncomputable def gaussianDensityAsym (a mass : ℝ) (φ : AsymLatticeField Nt Ns) : ℝ :=
  Real.exp (-(a ^ 2 / 2 : ℝ) * ∑ x : AsymLatticeSites Nt Ns,
    φ x * (massOperatorAsym Nt Ns a mass φ) x)

theorem gaussianDensityAsym_nonneg (a mass : ℝ) (φ : AsymLatticeField Nt Ns) :
    0 ≤ gaussianDensityAsym Nt Ns a mass φ :=
  le_of_lt (Real.exp_pos _)

theorem gaussianDensityAsym_measurable (a mass : ℝ) :
    Measurable (gaussianDensityAsym Nt Ns a mass) := by
  unfold gaussianDensityAsym
  exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finset_sum _ fun x _ =>
        (continuous_apply x).mul
          ((continuous_apply x).comp (massOperatorAsym Nt Ns a mass).continuous)))).measurable

/-- Spectral form of `gaussianDensityAsym` (diagonalised in the mass eigenbasis). -/
theorem gaussianDensityAsym_eq_exp_spectral (a mass : ℝ) (φ : AsymLatticeField Nt Ns) :
    gaussianDensityAsym Nt Ns a mass φ =
      Real.exp (-(a ^ 2 / 2 : ℝ) *
        ∑ k : AsymLatticeSites Nt Ns,
          massEigenvaluesAsym Nt Ns a mass k *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) ^ 2) := by
  unfold gaussianDensityAsym
  congr 2
  -- `∑ x, φ x · (Q φ) x = ∑ k, λ_k · c_k(φ)²`, the asym quadratic spectral identity.
  have hparseval := massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass φ
    (massOperatorAsym Nt Ns a mass φ)
  have hcoeff : ∀ k : AsymLatticeSites Nt Ns,
      (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
          (massOperatorAsym Nt Ns a mass φ) x) =
      massEigenvaluesAsym Nt Ns a mass k *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) := fun k =>
    massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff Nt Ns a mass φ k
  calc
    (∑ x : AsymLatticeSites Nt Ns, φ x * (massOperatorAsym Nt Ns a mass φ) x)
        = ∑ k : AsymLatticeSites Nt Ns,
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
                (massOperatorAsym Nt Ns a mass φ) x) := hparseval.symm
    _ = ∑ k : AsymLatticeSites Nt Ns,
          massEigenvaluesAsym Nt Ns a mass k *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [hcoeff k]; ring

noncomputable def gaussianDensityWeightAsym (a mass : ℝ) : AsymLatticeField Nt Ns → ENNReal :=
  fun φ => ENNReal.ofReal (gaussianDensityAsym Nt Ns a mass φ)

noncomputable def gaussianDensityMeasureAsym (a mass : ℝ) : Measure (AsymLatticeField Nt Ns) :=
  volume.withDensity (gaussianDensityWeightAsym Nt Ns a mass)

noncomputable def gaussianDensityNormConstAsym (a mass : ℝ) : ENNReal :=
  (gaussianDensityMeasureAsym Nt Ns a mass) Set.univ

noncomputable def normalizedGaussianDensityMeasureAsym (a mass : ℝ) :
    Measure (AsymLatticeField Nt Ns) :=
  (gaussianDensityNormConstAsym Nt Ns a mass)⁻¹ • gaussianDensityMeasureAsym Nt Ns a mass

/-! ### Coefficient reconstruction in the eigenbasis (asym) -/

theorem massEigenbasisAsym_coeff_reprSymm (a mass : ℝ)
    (v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns)) (k : AsymLatticeSites Nt Ns) :
    (∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
        ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v) x) = v k := by
  have hrepr := OrthonormalBasis.repr_apply_apply
    (b := massEigenvectorBasisAsym Nt Ns a mass)
    (v := (massEigenvectorBasisAsym Nt Ns a mass).repr.symm v) (i := k)
  have hleft :
      ((massEigenvectorBasisAsym Nt Ns a mass).repr
        ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v)).ofLp k = v k :=
    congrArg (fun w => w k)
      ((massEigenvectorBasisAsym Nt Ns a mass).repr.apply_symm_apply v)
  have hright :
      inner ℝ (massEigenvectorBasisAsym Nt Ns a mass k)
        ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v) =
      (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
          ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v) x) := by
    change ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp ⬝ᵥ
      star (massEigenvectorBasisAsym Nt Ns a mass k).ofLp = _
    simp [dotProduct, star_trivial, mul_comm]
  rw [hright] at hrepr
  exact (hleft.symm.trans hrepr).symm

theorem massEigenbasisAsym_coeff_reprSymm_ofLp (a mass : ℝ)
    (v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns)) (k : AsymLatticeSites Nt Ns) :
    (∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
        ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x) = v.ofLp k := by
  simpa using massEigenbasisAsym_coeff_reprSymm Nt Ns a mass v k

theorem massEigenbasisAsym_quadratic_sum_reprSymm_ofLp (a mass : ℝ)
    (v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns)) :
    (∑ k : AsymLatticeSites Nt Ns,
      massEigenvaluesAsym Nt Ns a mass k *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
            ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x) ^ 2) =
    ∑ k : AsymLatticeSites Nt Ns, massEigenvaluesAsym Nt Ns a mass k * (v.ofLp k) ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [massEigenbasisAsym_coeff_reprSymm_ofLp Nt Ns a mass v k]

theorem massEigenbasisAsym_linear_sum_reprSymm_ofLp (a mass : ℝ)
    (c : AsymLatticeSites Nt Ns → ℝ)
    (v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns)) :
    (∑ k : AsymLatticeSites Nt Ns, c k *
      (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
          ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x)) =
    ∑ k : AsymLatticeSites Nt Ns, c k * v.ofLp k := by
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [massEigenbasisAsym_coeff_reprSymm_ofLp Nt Ns a mass v k]

/-! ### Diagonal Gaussian Fourier integral in the asym eigenbasis -/

/-- Gaussian Fourier integral in mass-eigenbasis coordinates, with the
Glimm-Jaffe `a²/2` scaling on the quadratic term. Mirrors
`integral_massEigenbasis_cexp_GJ` from `Density.lean` with `d = 2`. -/
theorem integral_massEigenbasisAsym_cexp_GJ
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (c : AsymLatticeSites Nt Ns → ℝ) :
    (∫ φ : (AsymLatticeSites Nt Ns → ℝ),
      Complex.exp (-(a ^ 2 / 2 : ℂ) *
        ∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
            (↑(∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
        + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x)))) =
    ∏ k : AsymLatticeSites Nt Ns,
      (2 * Real.pi / ((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) *
          ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ))) := by
  classical
  let g : EuclideanSpace ℝ (AsymLatticeSites Nt Ns) → ℂ := fun v =>
    Complex.exp (-(a ^ 2 / 2 : ℂ) *
      ∑ k : AsymLatticeSites Nt Ns,
        (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
          (↑(∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * v x) : ℂ) ^ 2
      + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * v x)))
  let h : EuclideanSpace ℝ (AsymLatticeSites Nt Ns) → ℂ := fun v =>
    Complex.exp (-(a ^ 2 / 2 : ℂ) *
      ∑ k : AsymLatticeSites Nt Ns, (massEigenvaluesAsym Nt Ns a mass k : ℂ) * (v k : ℂ) ^ 2
      + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k * v k))
  let h' : EuclideanSpace ℝ (AsymLatticeSites Nt Ns) → ℂ := fun v =>
    Complex.exp (-(1 / 2 : ℂ) *
      ∑ k : AsymLatticeSites Nt Ns,
        (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ) * (v k : ℂ) ^ 2
      + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k * v k))
  have hstart :
      (∫ φ : (AsymLatticeSites Nt Ns → ℝ),
        Complex.exp (-(a ^ 2 / 2 : ℂ) *
          ∑ k : AsymLatticeSites Nt Ns,
            (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
              (↑(∑ x : AsymLatticeSites Nt Ns,
                (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
          + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x)))) =
      ∫ φ : (AsymLatticeSites Nt Ns → ℝ),
        g ((MeasurableEquiv.toLp 2 (AsymLatticeSites Nt Ns → ℝ)) φ) := by
    refine integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro φ
    simp [g]
  rw [hstart]
  have htolp :
      (∫ φ : (AsymLatticeSites Nt Ns → ℝ),
          g ((MeasurableEquiv.toLp 2 (AsymLatticeSites Nt Ns → ℝ)) φ)) =
      (∫ φ : (AsymLatticeSites Nt Ns → ℝ), g (WithLp.toLp 2 φ)) := by simp
  rw [htolp]
  rw [(PiLp.volume_preserving_toLp (AsymLatticeSites Nt Ns)).integral_comp
    (MeasurableEquiv.toLp 2 (AsymLatticeSites Nt Ns → ℝ)).measurableEmbedding]
  rw [← ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm.measurePreserving).integral_comp
    ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm.toHomeomorph.measurableEmbedding)]
  have hrepr : ∀ v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns),
      g ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v) = h v := by
    intro v
    have hqR :
        (∑ k : AsymLatticeSites Nt Ns,
          massEigenvaluesAsym Nt Ns a mass k *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
                ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x) ^ 2) =
        (∑ k : AsymLatticeSites Nt Ns, massEigenvaluesAsym Nt Ns a mass k * (v.ofLp k) ^ 2) :=
      massEigenbasisAsym_quadratic_sum_reprSymm_ofLp Nt Ns a mass v
    have hqC :
        (∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
            (↑(∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
                ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x) : ℂ) ^ 2) =
        (∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k : ℂ) * (v.ofLp k : ℂ) ^ 2) := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hqR
    have hlR :
        (∑ k : AsymLatticeSites Nt Ns, c k *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
              ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x)) =
        (∑ k : AsymLatticeSites Nt Ns, c k * v.ofLp k) :=
      massEigenbasisAsym_linear_sum_reprSymm_ofLp Nt Ns a mass c v
    have hlCcomplex :
        (↑(∑ k : AsymLatticeSites Nt Ns, c k *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
              ((massEigenvectorBasisAsym Nt Ns a mass).repr.symm v).ofLp x)) : ℂ) =
        (↑(∑ k : AsymLatticeSites Nt Ns, c k * v.ofLp k) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) hlR
    unfold g h
    rw [hqC, hlCcomplex]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrepr)]
  have hscale :
      (∫ v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns), h v) =
      ∫ v : EuclideanSpace ℝ (AsymLatticeSites Nt Ns), h' v := by
    refine integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro v
    unfold h h'
    congr 1
    have hsum :
        ((a ^ 2 : ℂ) *
          ∑ k : AsymLatticeSites Nt Ns,
            (massEigenvaluesAsym Nt Ns a mass k : ℂ) * (v k : ℂ) ^ 2) =
        (∑ k : AsymLatticeSites Nt Ns,
          (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ) * (v k : ℂ) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      norm_num
      ring
    calc
      -(a ^ 2 / 2 : ℂ) *
          ∑ k : AsymLatticeSites Nt Ns,
            (massEigenvaluesAsym Nt Ns a mass k : ℂ) * (v k : ℂ) ^ 2
          + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k * v k)
          =
        (-(1 / 2 : ℂ)) *
          ((a ^ 2 : ℂ) *
            ∑ k : AsymLatticeSites Nt Ns,
              (massEigenvaluesAsym Nt Ns a mass k : ℂ) * (v k : ℂ) ^ 2)
          + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k * v k) := by ring
      _ =
        (-(1 / 2 : ℂ)) *
          ∑ k : AsymLatticeSites Nt Ns,
            (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ) * (v k : ℂ) ^ 2
          + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k * v k) := by rw [hsum]
  rw [hscale]
  simpa [h'] using
    (integral_cexp_neg_half_sum_mul_sq_add_linear
      (ι := AsymLatticeSites Nt Ns)
      (lam := fun k => (a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k)
      (hlam := fun k => mul_pos (pow_pos ha 2)
        (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k))
      (c := c))

/-! ### The GJ-aligned covariance as a spectral sum (asym) -/

/-- The GJ-aligned asym covariance equals the rescaled spectral expansion:
`⟨T_GJ f, T_GJ g⟩ = (a²)⁻¹ Σ_k λ_k⁻¹ c_k(f) c_k(g)`. -/
theorem lattice_covariance_AsymGJ_eq_spectral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    GaussianField.covariance (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f g =
    (a ^ 2 : ℝ)⁻¹ *
    ∑ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) := by
  have ha2_pos : (0 : ℝ) < a ^ 2 := pow_pos ha 2
  have hsqrt_sq : Real.sqrt (a ^ 2) * Real.sqrt (a ^ 2) = a ^ 2 :=
    Real.mul_self_sqrt (le_of_lt ha2_pos)
  rw [← covariance_spectralLatticeCovarianceAsym_eq Nt Ns a mass ha hmass f g]
  unfold latticeCovarianceAsymGJ covariance
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  show (Real.sqrt (a ^ 2))⁻¹ *
        ((Real.sqrt (a ^ 2))⁻¹ *
          inner ℝ (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
            (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g)) =
      (a ^ 2 : ℝ)⁻¹ *
        inner ℝ (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
            (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g)
  rw [show (Real.sqrt (a ^ 2))⁻¹ * ((Real.sqrt (a ^ 2))⁻¹ *
        inner ℝ (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g)) =
      ((Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹) *
        inner ℝ (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
          (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g) from by ring]
  congr 1
  rw [show (Real.sqrt (a ^ 2))⁻¹ * (Real.sqrt (a ^ 2))⁻¹ =
      (Real.sqrt (a ^ 2) * Real.sqrt (a ^ 2))⁻¹ from by rw [mul_inv]]
  rw [hsqrt_sq]

/-! ### Site-pairing in eigenbasis coordinates (asym) -/

theorem sitePairingAsym_eq_massEigenbasis_sum (a mass : ℝ)
    (f φ : AsymLatticeField Nt Ns) :
    (∑ x : AsymLatticeSites Nt Ns, f x * φ x) =
      ∑ k : AsymLatticeSites Nt Ns,
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) :=
  (massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass f φ).symm

theorem measurable_sitePairingAsym (f : AsymLatticeField Nt Ns) :
    Measurable (fun φ : AsymLatticeField Nt Ns =>
      ∑ x : AsymLatticeSites Nt Ns, f x * φ x) := by
  simpa using
    (continuous_finset_sum _ (fun x _ => continuous_const.mul (continuous_apply x))).measurable

/-! ### Fourier identity, abstract side (asym) -/

/-- Fourier identity for the asym field law, in site coordinates (pushforward side). -/
theorem latticeGaussianFieldLawAsym_fourier (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) :
    ∫ φ : AsymLatticeField Nt Ns,
      Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
        ∂(latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f))) := by
  rw [latticeGaussianFieldLawAsym]
  have hmeas :
      AEStronglyMeasurable
        (fun φ : AsymLatticeField Nt Ns =>
          Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)))
        ((GaussianField.measure (latticeCovarianceAsymGJ Nt Ns a mass ha hmass)).map
          (evalMapAsym Nt Ns)) := by
    refine (Complex.continuous_exp.comp ?_).aestronglyMeasurable
    refine (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    exact continuous_finset_sum _ (fun x _ => continuous_const.mul (continuous_apply x))
  rw [integral_map (measurable_evalMapAsym Nt Ns).aemeasurable hmeas]
  have hcoord : ∀ ω : Configuration (AsymLatticeField Nt Ns),
      (∑ x : AsymLatticeSites Nt Ns, f x * (evalMapAsym Nt Ns ω) x) = ω f := by
    intro ω
    simpa using (config_apply_eq_sum_evalMapAsym Nt Ns ω f).symm
  simp_rw [hcoord]
  exact GaussianField.charFun (latticeCovarianceAsymGJ Nt Ns a mass ha hmass) f

/-! ### Fourier identity, density side (asym) -/

/-- Fourier identity for the normalized asym density measure (GJ-aligned). The hard
direction: diagonalise the quadratic form and apply the diagonal Gaussian integral. -/
theorem normalizedGaussianDensityMeasureAsym_linearFourier
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : AsymLatticeField Nt Ns) :
    ∫ φ : AsymLatticeField Nt Ns,
      Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
        ∂(normalizedGaussianDensityMeasureAsym Nt Ns a mass) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
      (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f))) := by
  classical
  let c : AsymLatticeSites Nt Ns → ℝ := fun k =>
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x
  let base : AsymLatticeSites Nt Ns → ℂ := fun k =>
    (2 * Real.pi / ((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k)) ^ (1 / 2 : ℂ)
  let expTerm : AsymLatticeSites Nt Ns → ℂ := fun k =>
    Complex.exp (-(1 / 2 : ℂ) *
      ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ)))
  have hnum :
      (∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) *
          gaussianDensityAsym Nt Ns a mass φ) =
      ∏ k : AsymLatticeSites Nt Ns, base k * expTerm k := by
    have hpoint :
        ∀ φ : AsymLatticeField Nt Ns,
          Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) *
            gaussianDensityAsym Nt Ns a mass φ =
          Complex.exp (-(a ^ 2 / 2 : ℂ) *
              ∑ k : AsymLatticeSites Nt Ns,
                (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
                  (↑(∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
            + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k *
                (∑ x : AsymLatticeSites Nt Ns,
                  (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x))) := by
      intro φ
      have hpair :
          (∑ x : AsymLatticeSites Nt Ns, f x * φ x) =
            ∑ k : AsymLatticeSites Nt Ns, c k *
              (∑ x : AsymLatticeSites Nt Ns,
                (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) := by
        simpa [c] using sitePairingAsym_eq_massEigenbasis_sum Nt Ns a mass f φ
      have hρ :
          gaussianDensityAsym Nt Ns a mass φ =
            Real.exp (-(a ^ 2 / 2 : ℝ) *
              ∑ k : AsymLatticeSites Nt Ns,
                massEigenvaluesAsym Nt Ns a mass k *
                  (∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) ^ 2) :=
        gaussianDensityAsym_eq_exp_spectral Nt Ns a mass φ
      rw [hpair, hρ]
      have hExp :
          (Complex.exp
            (-(a ^ 2 / 2 : ℂ) *
              ∑ k : AsymLatticeSites Nt Ns,
                (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
                  (↑(∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ)
                      ^ 2)) =
            (Real.exp (-(a ^ 2 / 2 : ℝ) *
              ∑ k : AsymLatticeSites Nt Ns,
                massEigenvaluesAsym Nt Ns a mass k *
                  (∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x)
                      ^ 2) : ℂ) := by
        simp
      rw [← hExp]
      rw [← Complex.exp_add]
      ring_nf
    calc
      (∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) *
          gaussianDensityAsym Nt Ns a mass φ)
          =
        ∫ φ : AsymLatticeField Nt Ns,
          Complex.exp (-(a ^ 2 / 2 : ℂ) *
              ∑ k : AsymLatticeSites Nt Ns,
                (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
                  (↑(∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
            + Complex.I * ↑(∑ k : AsymLatticeSites Nt Ns, c k *
                (∑ x : AsymLatticeSites Nt Ns,
                  (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x))) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall hpoint
      _ = ∏ k : AsymLatticeSites Nt Ns, base k * expTerm k := by
            simpa [base, expTerm] using
              integral_massEigenbasisAsym_cexp_GJ Nt Ns a mass ha hmass c
  have hdenC :
      (∫ φ : AsymLatticeField Nt Ns, (gaussianDensityAsym Nt Ns a mass φ : ℂ)) =
      ∏ k : AsymLatticeSites Nt Ns, base k := by
    have hpoint0 :
        ∀ φ : AsymLatticeField Nt Ns,
          (gaussianDensityAsym Nt Ns a mass φ : ℂ) =
            Complex.exp (-(a ^ 2 / 2 : ℂ) *
              ∑ k : AsymLatticeSites Nt Ns,
                (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
                  (↑(∑ x : AsymLatticeSites Nt Ns,
                    (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ)
                      ^ 2) := by
      intro φ
      rw [gaussianDensityAsym_eq_exp_spectral Nt Ns a mass φ]
      simp
    calc
      (∫ φ : AsymLatticeField Nt Ns, (gaussianDensityAsym Nt Ns a mass φ : ℂ))
          =
        ∫ φ : AsymLatticeField Nt Ns,
          Complex.exp (-(a ^ 2 / 2 : ℂ) *
            ∑ k : AsymLatticeSites Nt Ns,
              (massEigenvaluesAsym Nt Ns a mass k : ℂ) *
                (↑(∑ x : AsymLatticeSites Nt Ns,
                  (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ)
                    ^ 2) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall hpoint0
      _ = ∏ k : AsymLatticeSites Nt Ns, base k := by
            simpa [base] using integral_massEigenbasisAsym_cexp_GJ Nt Ns a mass ha hmass
              (fun _ => (0 : ℝ))
  have hbase_ne_zero : (∏ k : AsymLatticeSites Nt Ns, base k) ≠ 0 := by
    refine (Finset.prod_ne_zero_iff).2 ?_
    intro k _
    have hlamk : 0 < massEigenvaluesAsym Nt Ns a mass k :=
      massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k
    have hbaseArg :
        (2 * Real.pi / ((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k) : ℂ) ≠ 0 := by
      apply div_ne_zero
      · exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
      · exact_mod_cast (ne_of_gt (mul_pos (pow_pos ha 2) hlamk))
    have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hhalf).2 hbaseArg
  have hIntC : Integrable
      (fun φ : AsymLatticeField Nt Ns => (gaussianDensityAsym Nt Ns a mass φ : ℂ)) := by
    by_contra hnot
    have hz : (∫ φ : AsymLatticeField Nt Ns, (gaussianDensityAsym Nt Ns a mass φ : ℂ)) = 0 :=
      integral_undef hnot
    exact hbase_ne_zero (by simpa [hdenC] using hz)
  have hIntR : Integrable (gaussianDensityAsym Nt Ns a mass) := by
    simpa using hIntC.re
  have hnormConst :
      gaussianDensityNormConstAsym Nt Ns a mass =
        ENNReal.ofReal (∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ) := by
    simp [gaussianDensityNormConstAsym, gaussianDensityMeasureAsym, gaussianDensityWeightAsym]
    symm
    exact ofReal_integral_eq_lintegral_ofReal hIntR
      (Filter.Eventually.of_forall (gaussianDensityAsym_nonneg Nt Ns a mass))
  have hJcast' :
      (∫ φ : AsymLatticeField Nt Ns, (gaussianDensityAsym Nt Ns a mass φ : ℂ)) =
        ∏ k : AsymLatticeSites Nt Ns, base k := hdenC
  have hJ_ne_zero :
      (∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ) ≠ 0 := by
    intro h0
    have hIntCastZero :
        (∫ φ : AsymLatticeField Nt Ns, (gaussianDensityAsym Nt Ns a mass φ : ℂ)) = 0 := by
      simpa [h0] using (integral_complex_ofReal
        (f := fun φ : AsymLatticeField Nt Ns => gaussianDensityAsym Nt Ns a mass φ)
        (μ := (volume : Measure (AsymLatticeField Nt Ns))))
    exact hbase_ne_zero (by rw [← hJcast']; exact hIntCastZero)
  have hInv :
      ((gaussianDensityNormConstAsym Nt Ns a mass)⁻¹).toReal =
        (∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ)⁻¹ := by
    rw [hnormConst]
    have hnn : 0 ≤ ∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ :=
      integral_nonneg (fun φ => gaussianDensityAsym_nonneg Nt Ns a mass φ)
    simp [ENNReal.toReal_inv, hnn]
  have h_withDensity :
      (∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
          ∂(gaussianDensityMeasureAsym Nt Ns a mass)) =
      ∫ φ : AsymLatticeField Nt Ns,
        (gaussianDensityWeightAsym Nt Ns a mass φ).toReal •
          Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) := by
    have hflt : ∀ᵐ φ ∂(volume : Measure (AsymLatticeField Nt Ns)),
        gaussianDensityWeightAsym Nt Ns a mass φ < (⊤ : ENNReal) :=
      Filter.Eventually.of_forall (fun _ => by simp [gaussianDensityWeightAsym])
    simpa [gaussianDensityMeasureAsym] using
      (integral_withDensity_eq_integral_toReal_smul
        (μ := volume) (f := gaussianDensityWeightAsym Nt Ns a mass)
        (f_meas := by
          simpa [gaussianDensityWeightAsym] using
            (gaussianDensityAsym_measurable Nt Ns a mass).ennreal_ofReal)
        (hf_lt_top := hflt)
        (g := fun φ : AsymLatticeField Nt Ns =>
          Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))))
  have hprod_split :
      (∏ k : AsymLatticeSites Nt Ns, base k * expTerm k) =
        (∏ k : AsymLatticeSites Nt Ns, base k) *
          (∏ k : AsymLatticeSites Nt Ns, expTerm k) :=
    Finset.prod_mul_distrib
  have hExpProd :
      (∏ k : AsymLatticeSites Nt Ns, expTerm k) =
        Complex.exp (-(1 / 2 : ℂ) *
          ∑ k : AsymLatticeSites Nt Ns,
            ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ))) := by
    rw [← Complex.exp_sum]
    have hsum :
        (∑ k : AsymLatticeSites Nt Ns,
          (-(1 / 2 : ℂ)) *
            ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ))) =
        (-(1 / 2 : ℂ)) *
          (∑ k : AsymLatticeSites Nt Ns,
            ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ))) := by
      simp [Finset.mul_sum]
    simpa [expTerm] using congrArg Complex.exp hsum
  have hnorm_spec :
      (@inner ℝ ell2' _
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)) =
      (a ^ 2 : ℝ)⁻¹ *
        ∑ k : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k)⁻¹ * (c k) ^ 2 := by
    have h := lattice_covariance_AsymGJ_eq_spectral Nt Ns a mass ha hmass f f
    simp only [GaussianField.covariance] at h
    rw [h]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [c]
    ring
  have hnorm_cast :
      (↑(@inner ℝ ell2' _
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)) : ℂ) =
      ∑ k : AsymLatticeSites Nt Ns,
        ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ)) := by
    calc
      (↑(@inner ℝ ell2' _
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
        (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)) : ℂ)
          = ↑((a ^ 2 : ℝ)⁻¹ *
              ∑ k : AsymLatticeSites Nt Ns,
                (massEigenvaluesAsym Nt Ns a mass k)⁻¹ * (c k) ^ 2) := by rw [hnorm_spec]
      _ = (((a ^ 2 : ℝ)⁻¹ : ℂ) *
            ∑ k : AsymLatticeSites Nt Ns,
              (((massEigenvaluesAsym Nt Ns a mass k)⁻¹ * (c k) ^ 2 : ℝ) : ℂ)) := by simp
      _ = (((a ^ 2 : ℝ)⁻¹ : ℂ) *
            ∑ k : AsymLatticeSites Nt Ns,
              ((c k : ℂ) ^ 2 / (massEigenvaluesAsym Nt Ns a mass k : ℂ))) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro k _
            have hlamk : (massEigenvaluesAsym Nt Ns a mass k : ℂ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (massOperatorMatrixAsym_eigenvalues_pos
                Nt Ns a mass ha hmass k))
            calc
              (((massEigenvaluesAsym Nt Ns a mass k)⁻¹ * (c k) ^ 2 : ℝ) : ℂ)
                  = (c k : ℂ) ^ 2 * (massEigenvaluesAsym Nt Ns a mass k : ℂ)⁻¹ := by
                      norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
              _ = ((c k : ℂ) ^ 2 / (massEigenvaluesAsym Nt Ns a mass k : ℂ)) := by
                    simp [div_eq_mul_inv]
      _ = ∑ k : AsymLatticeSites Nt Ns,
            ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ)) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro k _
            have ha2_ne : ((a ^ 2 : ℝ) : ℂ) ≠ 0 := by
              exact_mod_cast (pow_ne_zero 2 (ne_of_gt ha))
            have hlamk : (massEigenvaluesAsym Nt Ns a mass k : ℂ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (massOperatorMatrixAsym_eigenvalues_pos
                Nt Ns a mass ha hmass k))
            push_cast
            field_simp
  calc
    ∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
          ∂(normalizedGaussianDensityMeasureAsym Nt Ns a mass)
        = ((gaussianDensityNormConstAsym Nt Ns a mass)⁻¹).toReal *
            ∫ φ : AsymLatticeField Nt Ns,
              Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
                ∂(gaussianDensityMeasureAsym Nt Ns a mass) := by
            simp [normalizedGaussianDensityMeasureAsym, gaussianDensityNormConstAsym,
              integral_smul_measure]
    _ = ((gaussianDensityNormConstAsym Nt Ns a mass)⁻¹).toReal *
          ∫ φ : AsymLatticeField Nt Ns,
            (gaussianDensityWeightAsym Nt Ns a mass φ).toReal •
              Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) := by
            rw [h_withDensity]
    _ = ((gaussianDensityNormConstAsym Nt Ns a mass)⁻¹).toReal *
          (∫ φ : AsymLatticeField Nt Ns,
            Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x)) *
              gaussianDensityAsym Nt Ns a mass φ) := by
            congr 1
            refine integral_congr_ae <| Filter.Eventually.of_forall ?_
            intro φ
            simp [gaussianDensityWeightAsym, gaussianDensityAsym_nonneg Nt Ns a mass φ, mul_comm]
    _ = ((gaussianDensityNormConstAsym Nt Ns a mass)⁻¹).toReal *
          (∏ k : AsymLatticeSites Nt Ns, base k * expTerm k) := by rw [hnum]
    _ = (((∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ)⁻¹ : ℝ) : ℂ) *
          (∏ k : AsymLatticeSites Nt Ns, base k * expTerm k) := by simp [hInv]
    _ = (((∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ)⁻¹ : ℝ) : ℂ) *
          ((∏ k : AsymLatticeSites Nt Ns, base k) *
            (∏ k : AsymLatticeSites Nt Ns, expTerm k)) := by rw [hprod_split]
    _ = (∏ k : AsymLatticeSites Nt Ns, expTerm k) := by
          rw [← hJcast']
          rw [integral_complex_ofReal]
          set J : ℝ := ∫ φ : AsymLatticeField Nt Ns, gaussianDensityAsym Nt Ns a mass φ
          have hJ0 : J ≠ 0 := by simpa [J] using hJ_ne_zero
          have hcancel : (((J⁻¹ : ℝ) : ℂ) * (J : ℂ)) = 1 := by
            exact_mod_cast (inv_mul_cancel₀ hJ0)
          rw [← mul_assoc, hcancel, one_mul]
    _ = Complex.exp (-(1 / 2 : ℂ) *
          ∑ k : AsymLatticeSites Nt Ns,
            ((c k : ℂ) ^ 2 / (((a ^ 2 : ℝ) * massEigenvaluesAsym Nt Ns a mass k : ℝ) : ℂ))) := by
          rw [hExpProd]
    _ = Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f))) := by rw [hnorm_cast]

/-! ### charFunDual match and finiteness (asym) -/

def strongDualToFieldAsym
    (L : StrongDual ℝ (AsymLatticeField Nt Ns)) : AsymLatticeField Nt Ns :=
  fun x => L (asymLatticeDelta Nt Ns x)

theorem strongDualAsym_apply_eq_site_sum
    (L : StrongDual ℝ (AsymLatticeField Nt Ns)) (φ : AsymLatticeField Nt Ns) :
    L φ = ∑ x : AsymLatticeSites Nt Ns, strongDualToFieldAsym Nt Ns L x * φ x := by
  conv_lhs => rw [asym_field_basis_decomp_density Nt Ns φ]
  simp [strongDualToFieldAsym, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- `charFunDual` rewritten in site coordinates (asym). -/
theorem charFunDualAsym_eq_site_integral
    (μ : Measure (AsymLatticeField Nt Ns))
    (L : StrongDual ℝ (AsymLatticeField Nt Ns)) :
    MeasureTheory.charFunDual μ L =
      ∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns,
          strongDualToFieldAsym Nt Ns L x * φ x)) ∂μ := by
  rw [MeasureTheory.charFunDual_eq_charFun_map_one]
  rw [MeasureTheory.charFun_apply_real]
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑(1 : ℝ) * ↑x * Complex.I))
        (μ.map L) := by
    refine (Complex.continuous_exp.comp ?_).aestronglyMeasurable
    exact ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  rw [integral_map L.continuous.measurable.aemeasurable hmeas]
  refine integral_congr_ae <| Filter.Eventually.of_forall ?_
  intro φ
  change Complex.exp (↑(1 : ℝ) * ↑(L φ) * Complex.I) =
    Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns,
      strongDualToFieldAsym Nt Ns L x * φ x))
  rw [strongDualAsym_apply_eq_site_sum Nt Ns L φ]
  simp [mul_comm]

/-- Characteristic-function identity between normalized asym density and the field law. -/
theorem normalizedGaussianDensityMeasureAsym_charFunDual_eq_latticeGaussianFieldLawAsym
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasureTheory.charFunDual (normalizedGaussianDensityMeasureAsym Nt Ns a mass) =
      MeasureTheory.charFunDual (latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) := by
  ext L
  rw [charFunDualAsym_eq_site_integral Nt Ns
      (μ := normalizedGaussianDensityMeasureAsym Nt Ns a mass) L]
  rw [charFunDualAsym_eq_site_integral Nt Ns
      (μ := latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) L]
  set f : AsymLatticeField Nt Ns := strongDualToFieldAsym Nt Ns L with hf
  calc
    ∫ φ : AsymLatticeField Nt Ns,
        Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
          ∂(normalizedGaussianDensityMeasureAsym Nt Ns a mass)
      = Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f)
          (latticeCovarianceAsymGJ Nt Ns a mass ha hmass f))) :=
          normalizedGaussianDensityMeasureAsym_linearFourier Nt Ns a mass ha hmass f
    _ = ∫ φ : AsymLatticeField Nt Ns,
          Complex.exp (Complex.I * ↑(∑ x : AsymLatticeSites Nt Ns, f x * φ x))
            ∂(latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) :=
          (latticeGaussianFieldLawAsym_fourier Nt Ns a mass ha hmass f).symm

/-- The normalized asym density measure is finite. -/
theorem normalizedGaussianDensityMeasureAsym_isFinite (a mass : ℝ) :
    MeasureTheory.IsFiniteMeasure (normalizedGaussianDensityMeasureAsym Nt Ns a mass) := by
  refine ⟨?_⟩
  set z : ENNReal := (gaussianDensityMeasureAsym Nt Ns a mass) Set.univ with hz_def
  have hz :
      (normalizedGaussianDensityMeasureAsym Nt Ns a mass) Set.univ = z⁻¹ * z := by
    simp [normalizedGaussianDensityMeasureAsym, gaussianDensityNormConstAsym, hz_def]
  rw [hz]
  by_cases h0 : z = 0
  · simp [h0]
  · by_cases htop : z = ⊤
    · simp [htop]
    · simp [ENNReal.inv_mul_cancel h0 htop]

/-! ### `normalizedGaussianDensityMeasureAsym` = `normalizedQuadraticGaussianMeasure` -/

/-- The intermediate normalized asym density measure is the generic normalized quadratic
Gaussian measure with precision `a² • massOperatorAsym` (the `d = 2` cell-area form). -/
theorem normalizedGaussianDensityMeasureAsym_eq_normalizedQuadraticGaussianMeasure
    (a mass : ℝ) :
    normalizedGaussianDensityMeasureAsym Nt Ns a mass =
      normalizedQuadraticGaussianMeasure (a ^ 2 • massOperatorAsym Nt Ns a mass) := by
  show (gaussianDensityNormConstAsym Nt Ns a mass)⁻¹ • gaussianDensityMeasureAsym Nt Ns a mass = _
  unfold gaussianDensityNormConstAsym normalizedQuadraticGaussianMeasure
    gaussianDensityMeasureAsym quadraticGaussianMeasure
  have h_density : gaussianDensityWeightAsym Nt Ns a mass =
      fun φ => ENNReal.ofReal
        (quadraticGaussianDensity (a ^ 2 • massOperatorAsym Nt Ns a mass) φ) := by
    funext φ
    unfold gaussianDensityWeightAsym gaussianDensityAsym quadraticGaussianDensity
    congr 1
    congr 1
    have h_smul : ∀ x : AsymLatticeSites Nt Ns,
        φ x * (((a ^ 2 : ℝ) • massOperatorAsym Nt Ns a mass) φ) x =
        a ^ 2 * (φ x * (massOperatorAsym Nt Ns a mass φ) x) := by
      intro x
      simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [h_smul]
    rw [← Finset.mul_sum]
    ring
  rw [h_density]

/-- **The asym density bridge (crux-1).** The free GFF, in coordinates, is the explicit
Lebesgue-density Gaussian with precision `a² • massOperatorAsym`.

Ported from `GaussianField/Density.lean` (square lattice), via the charFunDual match
(`MeasureTheory.Measure.ext_of_charFunDual`) and the intermediate
`normalizedGaussianDensityMeasureAsym`. -/
theorem latticeGaussianFieldLawAsym_eq_normalizedQuadraticGaussianMeasure
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    latticeGaussianFieldLawAsym Nt Ns a mass ha hmass =
      normalizedQuadraticGaussianMeasure (a ^ 2 • massOperatorAsym Nt Ns a mass) := by
  rw [← normalizedGaussianDensityMeasureAsym_eq_normalizedQuadraticGaussianMeasure Nt Ns a mass]
  letI : MeasureTheory.IsFiniteMeasure (normalizedGaussianDensityMeasureAsym Nt Ns a mass) :=
    normalizedGaussianDensityMeasureAsym_isFinite Nt Ns a mass
  letI : MeasureTheory.IsFiniteMeasure (latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) := by
    letI : MeasureTheory.IsProbabilityMeasure
        (latticeGaussianFieldLawAsym Nt Ns a mass ha hmass) := by
      rw [latticeGaussianFieldLawAsym]
      exact Measure.isProbabilityMeasure_map (measurable_evalMapAsym Nt Ns).aemeasurable
    infer_instance
  exact MeasureTheory.Measure.ext_of_charFunDual <|
    (normalizedGaussianDensityMeasureAsym_charFunDual_eq_latticeGaussianFieldLawAsym
      Nt Ns a mass ha hmass).symm

end GaussianField
