/-
# Lattice Field Theory

Gaussian field theory on lattices, both finite (periodic torus) and infinite
(ℤ^d with rapid decay). Provides:

1. Lattice site types and geometry (Sites)
2. Rapidly decaying functions on ℤ^d with DyninMityaginSpace structure (RapidDecayLattice)
3. Finite lattice field space with DyninMityaginSpace structure (FiniteField)
4. Discrete Laplacian with spacing parameter (Laplacian)
5. Covariance CLM and lattice Gaussian measure (Covariance)
6. FKG correlation inequality (FKG)

## Usage

```
import Lattice

variable (N : ℕ) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

-- The Gaussian measure on N×N lattice:
#check latticeGaussianMeasure 2 N a mass ha hmass
```
-/

import Lattice.Sites
import Lattice.RapidDecayLattice
import Lattice.FiniteField
import Lattice.Laplacian
import Lattice.Covariance
import Lattice.FKG
