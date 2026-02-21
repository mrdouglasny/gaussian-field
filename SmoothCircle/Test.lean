/-
  SmoothCircle/Test.lean

  End-to-end test: verify the Gaussian measure pipeline elaborates
  with `SmoothCircle L` and `SmoothCircle L ⊗ S(ℝ)` (cylinder) as test function spaces.
-/
import SmoothCircle.Nuclear
import SchwartzNuclear.HermiteNuclear
import GaussianField.Construction
import GaussianField.Properties

noncomputable section

open GaussianField TopologicalSpace

variable {L : ℝ} [Fact (0 < L)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-! ### Circle S¹_L -/

variable (T : SmoothCircle L →L[ℝ] H)

-- Core: measure exists and is a probability measure
#check GaussianField.measure T
#check GaussianField.measure_isProbability T

-- Characteristic functional
#check GaussianField.charFun T

-- Moments
#check GaussianField.pairing_is_gaussian T
#check GaussianField.measure_centered T
#check GaussianField.second_moment_eq_covariance T
#check GaussianField.cross_moment_eq_covariance T

/-! ### Cylinder S¹_L × ℝ via tensor product -/

/-- The cylinder test function space: C∞(S¹_L) ⊗̂ S(ℝ). -/
abbrev Cylinder (L : ℝ) [Fact (0 < L)] :=
  NuclearTensorProduct (SmoothCircle L) (SchwartzMap ℝ ℝ)

variable (S : Cylinder L →L[ℝ] H)

-- Core: measure exists and is a probability measure
#check GaussianField.measure S
#check GaussianField.measure_isProbability S

-- Characteristic functional
#check GaussianField.charFun S

-- Moments
#check GaussianField.pairing_is_gaussian S
#check GaussianField.measure_centered S
#check GaussianField.second_moment_eq_covariance S
#check GaussianField.cross_moment_eq_covariance S
