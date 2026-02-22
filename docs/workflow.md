# End-to-end workflow: from spaces to measures

The library has three layers. Layer 1 (test function spaces) and Layer 2
(covariance operators) are supplied by the user; Layer 3 (the measure and
all its properties) is produced automatically by the library.

```
Layer 1: Test function space E          [user provides DyninMityaginSpace instance]
Layer 2: Covariance operator T : E → H  [user constructs, typically via heat kernel]
Layer 3: measure T, charFun, moments    [library produces automatically]
```

## Layer 1: Define the test function space

Each space needs a `DyninMityaginSpace` instance. The instance specifies the
topology (via seminorms) and the Schauder basis used internally by the
construction. **The choice of basis does not affect the resulting measure** —
it only affects the internal proof machinery.

### Schwartz space $\mathcal{S}(\mathbb{R}^d)$ (implemented)

```lean
-- Fully proved in SchwartzNuclear/HermiteNuclear.lean (0 sorrys, 0 axioms)
instance : DyninMityaginSpace (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :=
  schwartz_dyninMityaginSpace _
```

### Circle $S^1$ of circumference $L$ (planned)

```lean
-- Smooth functions on the circle ℝ/Lℤ
structure SmoothMap_Circle (L : ℝ) (F : Type*) [Fact (0 < L)] := ...

instance : DyninMityaginSpace (SmoothMap_Circle L ℝ) where
  ι := ℕ                            -- single Sobolev index k
  p := sobolevSeminorm L             -- ‖f‖_k² = Σ_n (1+|n|)^{2k} |f̂_n|²
  basis := fourierBasis L             -- e^{2πinx/L} reindexed to ℕ
  coeff := fourierCoeff L             -- Fourier coefficients
  ...

-- Laplacian eigenvalues: λ_n = (2πn/L)² for the n-th Fourier mode
-- Circumference L is a parameter: it determines the eigenvalue spacing
```

### Finite periodic lattice with $N$ sites (planned)

```lean
-- N equally spaced points on a circle, with periodic boundary conditions
-- As a vector space this is just ℝ^N; periodicity enters through the Laplacian
abbrev PeriodicLattice (N : ℕ) := Fin N → ℝ

instance : DyninMityaginSpace (PeriodicLattice N) where
  ι := Unit                          -- single norm (finite-dim)
  basis := fun k => Pi.single k 1    -- standard basis
  ...                                -- trivial: finite-dim spaces are nuclear

-- Laplacian eigenvalues: λ_k = (2N/L)² sin²(πk/N) for spacing a = L/N
-- Lattice spacing a (or equivalently L and N) is NOT part of the
-- DyninMityaginSpace instance — it parameterizes the Laplacian operator
```

### Tensor products (implemented)

```lean
-- Generic: given DyninMityaginSpace E₁ and DyninMityaginSpace E₂, build E₁ ⊗̂ E₂
-- Defined as a Köthe sequence space — no abstract tensor product theory needed
def NuclearTensorProduct (E₁ E₂ : Type*) := RapidDecaySeq

-- Inherited DyninMityaginSpace instance (RapidDecaySeq is nuclear)
instance : DyninMityaginSpace (NuclearTensorProduct E₁ E₂) := ...

-- Pure tensor embedding: bilinear and jointly continuous
-- pure e₁ e₂ = m ↦ coeff(unpair(m).1, e₁) * coeff(unpair(m).2, e₂)
def pure (e₁ : E₁) (e₂ : E₂) : NuclearTensorProduct E₁ E₂ := ...
def pureLin : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] NuclearTensorProduct E₁ E₂ := ...
def pureCLM_right (e₁ : E₁) : E₂ →L[ℝ] NuclearTensorProduct E₁ E₂ := ...
theorem pure_continuous : Continuous (fun p : E₁ × E₂ => pure p.1 p.2) := ...

-- Specific product spaces are abbreviations:
abbrev Torus2 (L₁ L₂) := NuclearTensorProduct (SmoothMap_Circle L ℝ₁) (SmoothMap_Circle L ℝ₂)
abbrev Cylinder (L) := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ¹ ℝ)
```

## Layer 2: Build the covariance operator $T$

The operator $T : E \to H$ determines the specific Gaussian measure —
its covariance, its support properties, its physical interpretation.
The library doesn't prescribe how $T$ is built; it accepts any CLM.

In QFT, $T$ is typically a function of the Laplacian: $T = f(-\Delta + m^2)$,
most commonly $f(x) = x^{-1/2}$ for the Gaussian free field.

### The heat kernel as the fundamental building block

On product spaces, the Laplacian decomposes additively:

$$-\Delta_{M_1 \times M_2} = (-\Delta_{M_1}) \otimes I + I \otimes (-\Delta_{M_2})$$

The covariance operator $(-\Delta + m^2)^{-1/2}$ is a nonlinear function of
this sum and **does not factor** as a tensor product $T_1 \otimes T_2$.

The **heat kernel** $e^{-s(-\Delta + m^2)}$ is better because it **does factor**:

$$e^{-s(A_1 \otimes I + I \otimes A_2)} = e^{-sA_1} \otimes e^{-sA_2}$$

This follows from commutativity of the Kronecker factors ($A_1 \otimes I$
and $I \otimes A_2$ commute) and `exp_add_of_commute` (already in Mathlib).

The heat kernel serves directly as a covariance operator: set $T_s = e^{-sA/2}$
to get covariance $C_s(f,g) = \langle f, e^{-sA} g \rangle$. The standard GFF
covariance is recovered by integration:

$$\langle f, A^{-1} g \rangle = \int_0^\infty \langle f, e^{-sA} g \rangle\, ds$$

### Heat kernels on each space

**Schwartz space / continuum $\mathbb{R}^d$.** The heat kernel
$e^{s\Delta}$ acts on Hermite functions by $e^{-s\lambda_m}$ where
$\lambda_m = 2m + d$. It maps $\mathcal{S}(\mathbb{R}^d)$ to itself
and is a bounded operator on $L^2(\mathbb{R}^d)$.

**Circle $S^1_L$.** The heat kernel acts on Fourier modes by
$e^{-s(2\pi n/L)^2}$. The circumference $L$ enters through the
eigenvalue spacing.

**Periodic lattice.** The discrete heat kernel is the matrix exponential
$e^{-s\Delta_{\text{disc}}}$ where $\Delta_{\text{disc}}$ is the discrete
periodic Laplacian with eigenvalues $\lambda_k = (2N/L)^2 \sin^2(\pi k/N)$.
Mathlib provides `Matrix.exp` for this.

```lean
-- Heat kernel on a finite lattice
def heatKernel (A : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :=
  Matrix.exp ℝ ((-s) • A)

-- Key property: factors over Kronecker products
theorem heatKernel_product (A₁ A₂ s) :
    heatKernel (kron A₁ 1 + kron 1 A₂) s =
      kron (heatKernel A₁ s) (heatKernel A₂ s)

-- Mass factors out as a scalar
theorem heatKernel_massive (Δ m s) :
    heatKernel (Δ + m^2 • 1) s = exp(-m²s) • heatKernel Δ s
```

### Constructing $T$ on a product space

Here is the recipe for the massive GFF on a product lattice $\Lambda_1 \times \Lambda_2$:

```lean
-- Step 1: Define the Laplacian on each factor
def Δ₁ := discretePeriodicLaplacian L₁ N₁   -- eigenvalues from spacing L₁/N₁
def Δ₂ := discretePeriodicLaplacian L₂ N₂   -- eigenvalues from spacing L₂/N₂

-- Step 2: Form the product Laplacian + mass
def A := kron Δ₁ 1 + kron 1 Δ₂ + mass^2 • 1

-- Step 3: Heat kernel at "time" s gives the covariance operator
def T := matrixToCLM (heatKernel A (s/2))

-- By heatKernel_product and heatKernel_massive:
-- T = exp(-m²s/2) • kron (heatKernel Δ₁ (s/2)) (heatKernel Δ₂ (s/2))
-- The product structure is manifest.
```

For the continuum, the same pattern applies — replace `Matrix.exp` with the
operator exponential in the appropriate Banach algebra.

For a single (non-product) operator, Mathlib's continuous functional calculus
gives $T = A^{-1/2}$ directly via `CFC.rpow`, without needing the heat kernel.

## Layer 3: The library produces the measure

Once you have `[DyninMityaginSpace E]` and `T : E →L[ℝ] H`, everything else is automatic:

```lean
open GaussianField in

-- The Gaussian probability measure on E' = WeakDual ℝ E
#check measure T                             -- Measure (Configuration E)
#check instIsProbabilityMeasureMeasure T     -- IsProbabilityMeasure

-- Characteristic functional: E[exp(iω(f))] = exp(-½‖Tf‖²)
#check charFun T

-- Marginals are 1D Gaussians
#check pairing_is_gaussian T                 -- pushforward by ω↦ω(f) is N(0,‖Tf‖²)

-- Moments
#check measure_centered T                    -- E[ω(f)] = 0
#check second_moment_eq_covariance T         -- E[ω(f)²] = ‖Tf‖² = C(f,f)
#check cross_moment_eq_covariance T          -- E[ω(f)ω(g)] = ⟨Tf,Tg⟩ = C(f,g)

-- Integrability (Fernique-type)
#check pairing_integrable T                  -- ω(f) is integrable
#check pairing_memLp T                       -- ω(f) ∈ Lᵖ for all finite p
#check pairing_product_integrable T          -- ω(f)·ω(g) is integrable

-- Mathlib IsGaussian instance
#check measure_isGaussian T                  -- IsGaussian (measure T)
```

## Full example: lattice GFF on a 2-torus

Putting all three layers together for the massive Gaussian free field
on a $2$-torus with side lengths $L_1, L_2$ and lattice spacings
$a_i = L_i / N_i$:

```lean
variable (L₁ L₂ : ℝ) [Fact (0 < L₁)] [Fact (0 < L₂)]
variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂]
variable (mass s : ℝ) (hs : 0 < s)

-- Layer 1: test function space = ℝ^{N₁ × N₂}  (trivially nuclear)
abbrev E := Fin N₁ × Fin N₂ → ℝ
instance : DyninMityaginSpace E := ...

-- Layer 2: T = e^{-s(-Δ₁⊗I - I⊗Δ₂ + m²)/2}
def Δ₁ := discretePeriodicLaplacian L₁ N₁
def Δ₂ := discretePeriodicLaplacian L₂ N₂
def A  := kron Δ₁ 1 + kron 1 Δ₂ + mass^2 • 1
def T  := matrixToCLM (heatKernel A (s / 2))

-- Layer 3: the library gives us everything
-- μ = centered Gaussian on (Fin N₁ × Fin N₂ → ℝ)' with covariance
--   C(f,g) = ⟨f, e^{-sA} g⟩ = e^{-m²s} ⟨f, e^{-sΔ₁} ⊗ e^{-sΔ₂} g⟩
def μ := GaussianField.measure T

-- All properties are inherited:
-- μ is a probability measure
-- E_μ[ω(f)] = 0
-- E_μ[ω(f)ω(g)] = ⟨Tf, Tg⟩ = ⟨f, e^{-sA} g⟩
-- ω(f) ∈ Lᵖ(μ) for all p
```

## Continuum limit

To take the continuum limit $a \to 0$ (i.e., $N \to \infty$ with $L$ fixed),
the characteristic functional identity reduces the problem to:

$$\|T_N(r_N f)\|^2 \to \|T(f)\|^2 \qquad \forall f \in E_{\text{continuum}}$$

where $r_N : E_{\text{continuum}} \to E_N$ restricts a smooth function to lattice
points. See [lattice-continuum limit](lattice-continuum-limit.md) for details.
