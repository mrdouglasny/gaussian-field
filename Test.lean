/-
  SmoothMap_Circle/Test.lean

  End-to-end tests: verify the Gaussian measure pipeline elaborates for
  all concrete nuclear space instances and their tensor products.
-/
import SmoothCircle.Nuclear
import SchwartzNuclear.HermiteNuclear
import GaussianField.Construction
import GaussianField.Properties
import GaussianField.IsGaussian
import HeatKernel
-- import HeatKernel.PositionKernel  -- moved to future/

noncomputable section

open GaussianField TopologicalSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-! ### Schwartz space S(ℝ) -/

section Schwartz1D
variable (T : SchwartzMap ℝ ℝ →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.pairing_is_gaussian T
#check GaussianField.measure_centered T
#check GaussianField.second_moment_eq_covariance T
#check GaussianField.cross_moment_eq_covariance T
#check GaussianField.measure_isGaussian T
end Schwartz1D

/-! ### Schwartz space S(ℝᵈ) -/

section SchwartzMultiD
variable {d : ℕ}
variable (T : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.measure_isGaussian T
end SchwartzMultiD

/-! ### Circle S¹_L -/

section Circle
variable {L : ℝ} [Fact (0 < L)]
variable (T : SmoothMap_Circle L ℝ →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.pairing_is_gaussian T
#check GaussianField.measure_centered T
#check GaussianField.second_moment_eq_covariance T
#check GaussianField.cross_moment_eq_covariance T
#check GaussianField.measure_isGaussian T
end Circle

/-! ### Cylinder S¹_L × ℝ -/

section Cylinder
variable {L : ℝ} [Fact (0 < L)]

abbrev Cylinder (L : ℝ) [Fact (0 < L)] :=
  NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)

variable (T : Cylinder L →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.measure_isGaussian T
end Cylinder

/-! ### Torus T² = S¹_{L₁} × S¹_{L₂} -/

section Torus
variable {L₁ L₂ : ℝ} [Fact (0 < L₁)] [Fact (0 < L₂)]

abbrev Torus (L₁ L₂ : ℝ) [Fact (0 < L₁)] [Fact (0 < L₂)] :=
  NuclearTensorProduct (SmoothMap_Circle L₁ ℝ) (SmoothMap_Circle L₂ ℝ)

variable (T : Torus L₁ L₂ →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.measure_isGaussian T
end Torus

/-! ### Schwartz tensor product S(ℝ) ⊗̂ S(ℝ) -/

section SchwartzTensor
abbrev SchwartzProduct :=
  NuclearTensorProduct (SchwartzMap ℝ ℝ) (SchwartzMap ℝ ℝ)

variable (T : SchwartzProduct →L[ℝ] H)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.measure_isGaussian T
end SchwartzTensor

/-! ### Finite-dimensional Hilbert space (degenerate case, H = ℝ) -/

section FiniteDim
variable {L : ℝ} [Fact (0 < L)]
variable (T : SmoothMap_Circle L ℝ →L[ℝ] ℝ)

#check GaussianField.measure T
#check GaussianField.measure_isProbability T
#check GaussianField.charFun T
#check GaussianField.measure_isGaussian T
end FiniteDim

/-! ### Standard 2D QFT on the cylinder S¹_L × ℝ

The free massive scalar field on the cylinder S¹_L × ℝ with mass m > 0.
The covariance operator is T = (-Δ + m²)^{-1/2} : E → ℓ², where
E = C^∞(S¹_L) ⊗̂ 𝓢(ℝ) is the nuclear tensor product test function space.

The DyninMityaginSpace basis for E is ℕ-indexed (via Cantor pairing of the
Fourier basis on S¹_L with the Hermite basis on ℝ). Mode m = ⟨n, k⟩ has:
- Fourier eigenvalue (2πn/L)² from -d²/dθ²
- Harmonic oscillator eigenvalue (2k+1) from -d²/dx² + x²
- Mass contribution m²

The covariance CLM maps f ↦ (σ_m · coeff_m(f))_m ∈ ℓ² where
σ_m = eigenvalue(m)^{-1/2} are the singular values. Constructed via
`spectralCLM` from `HeatKernel.Axioms`.
-/

section QFT2D_Cylinder

open GaussianField

variable {L : ℝ} [Fact (0 < L)]

/-- The covariance CLM: T(f)_m = σ_m · coeff_m(f).

    Built from `spectralCLM` with the QFT singular values
    σ_m = ((2πn/L)² + (2k+1) + mass²)^{-1/2} where (n,k) = Nat.unpair m.

    Satisfies: (T f)_m = qftSingularValue L mass m · coeff_m(f). -/
noncomputable def qftCovarianceCLM (mass : ℝ) (hmass : 0 < mass) :
    Cylinder L →L[ℝ] ell2' :=
  spectralCLM
    (fun m => qftSingularValue L mass m)
    (qft_singular_values_bounded L mass (Fact.out) hmass)

/-- The 2D QFT Gaussian measure on the cylinder.

    Centered Gaussian probability measure on (C^∞(S¹_L) ⊗̂ 𝓢(ℝ))'
    with covariance C(f,g) = ⟨f, (-Δ + m²)⁻¹ g⟩. -/
noncomputable def qftMeasure (mass : ℝ) (hmass : 0 < mass) :
    @MeasureTheory.Measure (Configuration (Cylinder L))
      GaussianField.instMeasurableSpaceConfiguration :=
  GaussianField.measure (qftCovarianceCLM mass hmass)

-- Verify the full Gaussian field API elaborates for the concrete 2D QFT

section QFT2D_Tests
variable (mass : ℝ) (hmass : 0 < mass)

-- The measure is a probability measure
#check GaussianField.measure_isProbability (qftCovarianceCLM (L := L) mass hmass)

-- Characteristic functional: E[exp(iω(f))] = exp(-½‖T(f)‖²)
#check GaussianField.charFun (qftCovarianceCLM (L := L) mass hmass)

-- Each pairing ω(f) is Gaussian
#check GaussianField.pairing_is_gaussian (qftCovarianceCLM (L := L) mass hmass)

-- The measure is centered: E[ω(f)] = 0
#check GaussianField.measure_centered (qftCovarianceCLM (L := L) mass hmass)

-- Second moment = covariance: E[ω(f)²] = ‖T(f)‖²
#check GaussianField.second_moment_eq_covariance (qftCovarianceCLM (L := L) mass hmass)

-- Cross moment: E[ω(f)ω(g)] = ⟨T(f), T(g)⟩
#check GaussianField.cross_moment_eq_covariance (qftCovarianceCLM (L := L) mass hmass)

-- The measure is Gaussian (the full IsGaussian predicate)
#check GaussianField.measure_isGaussian (qftCovarianceCLM (L := L) mass hmass)

end QFT2D_Tests

/-- The covariance bilinear form of the 2D QFT.

    C(f, g) = ⟨T(f), T(g)⟩_ℓ² = ∑_m σ_m² · coeff_m(f) · coeff_m(g)
            = ∑_m coeff_m(f) · coeff_m(g) / eigenvalue(m)
            = ⟨f, (-Δ + m²)⁻¹ g⟩

    This is the Green's function of the massive Laplacian on S¹_L × ℝ. -/
noncomputable def qftCovariance (mass : ℝ) (hmass : 0 < mass)
    (f g : Cylinder L) : ℝ :=
  GaussianField.covariance (qftCovarianceCLM mass hmass) f g

/-- The covariance decomposes as an ℓ² inner product of spectral coefficients. -/
theorem qftCovariance_eq_inner (mass : ℝ) (hmass : 0 < mass)
    (f g : Cylinder L) :
    qftCovariance mass hmass f g =
      @inner ℝ ell2' _ (qftCovarianceCLM mass hmass f)
        (qftCovarianceCLM mass hmass g) :=
  rfl

end QFT2D_Cylinder

/-! ### Heat-regularized 2D QFT on the cylinder

The heat-regularized covariance T_s = e^{-s(-Δ+m²)/2} provides a
one-parameter family of Gaussian measures interpolating between the
identity (s=0) and the GFF covariance (s→∞).

The singular values e^{-s·eigenvalue(m)/2} decay exponentially,
making T_s trace class for all s > 0. -/

section HeatRegularized

open GaussianField

variable {L : ℝ} [Fact (0 < L)]

/-- Heat-regularized covariance CLM: T_s(f)_m = e^{-sλ_m/2} · coeff_m(f).

    Built from `spectralCLM` with heat singular values e^{-sλ_m/2}.
    For s > 0 this is trace class (exponential decay).
    At s = 0 this is the identity (in the basis representation). -/
noncomputable def heatCovarianceCLM (mass : ℝ) (hmass : 0 < mass)
    (s : ℝ) (hs : 0 ≤ s) : Cylinder L →L[ℝ] ell2' :=
  spectralCLM
    (fun m => heatSingularValue L mass s m)
    (heat_singular_values_bounded L mass (Fact.out) hmass s hs)

/-- The heat-regularized Gaussian measure on the cylinder. -/
noncomputable def heatMeasure (mass : ℝ) (hmass : 0 < mass)
    (s : ℝ) (hs : 0 ≤ s) :
    @MeasureTheory.Measure (Configuration (Cylinder L))
      GaussianField.instMeasurableSpaceConfiguration :=
  GaussianField.measure (heatCovarianceCLM mass hmass s hs)

-- Verify the API elaborates for the heat-regularized version
section HeatTests
variable (mass : ℝ) (hmass : 0 < mass) (s : ℝ) (hs : 0 ≤ s)

#check GaussianField.measure (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.measure_isProbability (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.charFun (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.pairing_is_gaussian (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.measure_centered (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.second_moment_eq_covariance (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.cross_moment_eq_covariance (heatCovarianceCLM (L := L) mass hmass s hs)
#check GaussianField.measure_isGaussian (heatCovarianceCLM (L := L) mass hmass s hs)

end HeatTests

/-- The heat covariance CLM specifies coordinates via spectralCLM_coord. -/
theorem heatCovarianceCLM_coord (mass : ℝ) (hmass : 0 < mass)
    (s : ℝ) (hs : 0 ≤ s) (f : Cylinder L) (m : ℕ) :
    (heatCovarianceCLM mass hmass s hs f : ℕ → ℝ) m =
      heatSingularValue L mass s m * DyninMityaginSpace.coeff m f :=
  spectralCLM_coord _ _ f m

/-- The QFT covariance CLM specifies coordinates. -/
theorem qftCovarianceCLM_coord (mass : ℝ) (hmass : 0 < mass)
    (f : Cylinder L) (m : ℕ) :
    (qftCovarianceCLM mass hmass f : ℕ → ℝ) m =
      qftSingularValue L mass m * DyninMityaginSpace.coeff m f :=
  spectralCLM_coord _ _ f m

end HeatRegularized

/-! ### Position-space heat kernel on the cylinder

The heat kernel K((θ₁,x₁), (θ₂,x₂), t) is defined as a factored product:
  K = e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t)
where K_circle is the circle heat kernel (periodized Gaussian) and K_osc
is the Mehler kernel (harmonic oscillator heat kernel).

These tests verify:
1. All definitions and axioms elaborate correctly
2. Key derived properties (symmetry, positivity, periodicity) type-check
3. The bridge theorem connecting position-space to spectral CLM elaborates
-/

-- PositionKernel section moved to future/ (contains mehlerKernel_eq_series axiom)
