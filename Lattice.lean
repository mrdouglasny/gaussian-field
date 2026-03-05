/-
# Lattice Field Theory

Gaussian field theory on lattices, both finite (periodic torus) and infinite
(ℤ^d with rapid decay). Provides:

1. Lattice site types and geometry (Sites)
2. Torus embedding: discrete lattice to continuous torus (TorusEmbedding)
3. Rapidly decaying functions on ℤ^d with DyninMityaginSpace structure (RapidDecayLattice)
4. Finite lattice field space with DyninMityaginSpace structure (FiniteField)
5. Discrete Laplacian with spacing parameter (Laplacian)
6. Covariance CLM and lattice Gaussian measure (Covariance)
7. FKG correlation inequality (FKG)

## Usage

```
import Lattice

variable (N : ℕ) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

-- The Gaussian measure on N×N lattice:
#check latticeGaussianMeasure 2 N a mass ha hmass
```
-/

import Lattice.Sites
import Lattice.TorusEmbedding
import Lattice.RapidDecayLattice
import Lattice.FiniteField
import Lattice.Laplacian
import Lattice.HeatKernel
import Lattice.Symmetry
import Lattice.Covariance
import Lattice.FKG
