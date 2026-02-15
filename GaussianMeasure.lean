-- GaussianMeasure: Construction of Gaussian measures on duals of Schwartz spaces
--
-- Given a CLM T : S(D,F) → H from a Schwartz space to a separable
-- infinite-dimensional Hilbert space, constructs a probability measure μ
-- on S'(D,F) = WeakDual ℝ (SchwartzMap D F) with characteristic functional
--   E[exp(i⟨ω, f⟩)] = exp(-½ ‖T(f)‖²)

import GaussianMeasure.Axioms
import GaussianMeasure.SpectralTheorem
import GaussianMeasure.NuclearSVD
import GaussianMeasure.NuclearFactorization
import GaussianMeasure.TargetFactorization
import GaussianMeasure.SeriesConvergence
import GaussianMeasure.Construction
import GaussianMeasure.Properties
