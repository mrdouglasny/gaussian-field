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
module

public import Lattice.Sites
public import Lattice.TorusEmbedding
public import Lattice.RapidDecayLattice
public import Lattice.FiniteField
public import Lattice.Laplacian
public import Lattice.HeatKernel
public import Lattice.Symmetry
public import Lattice.Covariance
public import Lattice.Convergence
public import Lattice.HeatKernelConvergence1d
public import Lattice.FKG
public import Lattice.CombesThomas
