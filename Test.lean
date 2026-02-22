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
