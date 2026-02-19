# gaussian-field

A Lean 4 / Mathlib library for constructing **centered Gaussian probability measures on duals of nuclear Fréchet spaces**.

Given a nuclear Fréchet space $E$ and a continuous linear map (CLM) $T : E \to H$ to a separable real Hilbert space $H$ (finite- or infinite-dimensional), the library constructs a probability measure $\mu$ on the weak dual $E' = \text{WeakDual}\ \mathbb{R}\ E$ satisfying the characteristic functional identity:

$$\mathbb{E}\left[e^{i\langle\omega, f\rangle}\right] = e^{-\frac{1}{2}\|T(f)\|_H^2} \qquad \forall f \in E$$

The covariance is $C(f,g) = \langle T(f), T(g) \rangle_H$.

## Motivation

This construction is the standard path to Gaussian measures in quantum field theory, stochastic PDEs, and infinite-dimensional probability. The library is **application-agnostic** — it works for any nuclear Fréchet space and any CLM into any separable Hilbert space.

### Example: Gaussian Free Field

For the free scalar field in $d$ dimensions, take:
- $E = \mathcal{S}(\mathbb{R}^d, \mathbb{R})$ (Schwartz space, a nuclear Fréchet space)
- $H = L^2(\mathbb{R}^d)$
- $T = (-\Delta + m^2)^{-1/2}$ (inverse half-Laplacian on Schwartz space)

The resulting measure is the Gaussian free field with mass $m$, and the covariance is:
$$C(f,g) = \int \frac{\hat{f}(p)\,\overline{\hat{g}(p)}}{|p|^2 + m^2}\,dp$$

### Gel'fand Triple Structure

The construction realizes a **rigged Hilbert space** (Gel'fand triple):

$$E \hookrightarrow H_T \hookrightarrow E'$$

where $H_T$ is the **Cameron-Martin space** — the completion of $E$ under the inner product $\langle f, g \rangle_T = \langle T(f), T(g) \rangle_H = C(f,g)$. The measure $\mu$ is supported on $E'$ but concentrated (in the sense of regularity) on distributions with specific Sobolev/Besov regularity determined by $T$.

This triple is the functional-analytic core of:
- **Constructive QFT**: the Osterwalder-Schrader and Wightman frameworks, where $\mu$ is the Euclidean path integral measure
- **Stochastic PDEs**: where $\mu$ provides the law of Gaussian driving noise
- **Infinite-dimensional probability**: where $\mu$ generalizes finite-dimensional Gaussian distributions

## API

### Input

The user provides:
- A nuclear Fréchet space `E` with `[NuclearSpace E]` instance
- A separable real Hilbert space `H` (with standard Mathlib instances)
- A CLM `T : E →L[ℝ] H`

### Output

| Definition / Theorem | Type | Description |
|---|---|---|
| `measure T` | `Measure (Configuration E)` | The Gaussian measure (with `IsProbabilityMeasure` instance) |
| `covariance T f g` | `ℝ` | $C(f,g) = \langle T(f), T(g) \rangle_H$ |
| `charFun T f` | integral identity | $\mathbb{E}[e^{i\omega(f)}] = e^{-\frac{1}{2}\|Tf\|^2}$ |
| `pairing_is_gaussian` | measure equality | Pushforward by $\omega \mapsto \omega(f)$ is $N(0, \|Tf\|^2)$ |
| `measure_centered` | integral = 0 | $\mathbb{E}[\omega(f)] = 0$ |
| `second_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)^2] = \|Tf\|^2$ |
| `cross_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)\omega(g)] = \langle Tf, Tg \rangle$ |
| `pairing_integrable` | `Integrable` | $\omega(f)$ is integrable |
| `pairing_memLp` | `MemLp` | $\omega(f) \in L^p$ for all finite $p$ (Fernique-type) |
| `pairing_product_integrable` | `Integrable` | $\omega(f)\omega(g)$ is integrable |

### Design notes

The API takes only `T` as an explicit argument — no proof of infinite-dimensionality
is required. When `H` is finite-dimensional, the construction embeds `H` isometrically
into $\ell^2$ and builds the measure there, yielding a degenerate (finite-rank) Gaussian.
This allows testing with toy cases like $H = \mathbb{R}^n$.

`Configuration E` is defined as `WeakDual ℝ E` — the space of continuous linear functionals on $E$ with the weak-* topology. Elements $\omega \in E'$ are "configurations" or "generalized functions" that pair with test functions: $\omega(f) \in \mathbb{R}$.

## The `NuclearSpace` typeclass

The core abstraction is the `NuclearSpace` typeclass, which encodes the Dynin-Mityagin structure: a nuclear Fréchet space with a countable Schauder basis admitting polynomial growth and super-polynomial decay estimates.

```lean
class NuclearSpace (E : Type*)
    [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] where
  ι : Type*                           -- seminorm index type
  p : ι → Seminorm ℝ E               -- the seminorm family
  h_with : WithSeminorms p            -- topology = seminorm topology
  basis : ℕ → E                       -- Schauder basis {ψ_m}
  coeff : ℕ → (E →L[ℝ] ℝ)           -- coefficient CLMs {c_m}
  expansion :                          -- scalar expansion identity
    ∀ (φ : E →L[ℝ] ℝ) (f : E), φ f = ∑' m, (coeff m f) * φ (basis m)
  basis_growth :                       -- polynomial growth of seminorms
    ∀ (i : ι), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, p i (basis m) ≤ C * (1 + (m : ℝ)) ^ s
  coeff_decay :                        -- super-polynomial decay of coefficients
    ∀ (k : ℕ), ∃ C > 0, ∃ (q : ι),
    ∀ f m, |coeff m f| * (1 + (m : ℝ)) ^ k ≤ C * p q f
```

### Key design decisions

- **Locally convex mixins** (`AddCommGroup`, `Module ℝ`, `TopologicalSpace`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`) rather than `NormedAddCommGroup`. Fréchet spaces are not normable.
- **Bundled seminorms.** The `ι` and `p` are fields, not class parameters, so `[NuclearSpace E]` works in theorem signatures without specifying the seminorm family.
- **Scalar expansion.** The expansion axiom tests against `φ : E →L[ℝ] ℝ`, not arbitrary Hilbert spaces. This avoids universe polymorphism issues. The Hilbert-space form is recovered as the 3-line lemma `NuclearSpace.expansion_H`.
- **ℕ exponents.** Polynomial bounds use `k : ℕ` and `pow`, avoiding `Real.rpow` pain.

## Providing a `NuclearSpace` instance for a new space

To use this library with a function space other than Schwartz space, provide a `NuclearSpace` instance. Here is what you need:

### Prerequisites (Mathlib instances)

Your space `E` must carry the locally convex TVS mixins:
```lean
variable (E : Type*) [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
```

### What to provide

| Field | What it means | What to supply |
|---|---|---|
| `ι` | Seminorm index type | e.g., `ℕ × ℕ` for Schwartz, `ℕ` for Sobolev-type |
| `p` | Seminorm family | `ι → Seminorm ℝ E` generating the Fréchet topology |
| `h_with` | Topology agreement | `WithSeminorms p` — proves the topology on `E` equals the seminorm topology |
| `basis` | Schauder basis | `ℕ → E` — a countable basis for `E` |
| `coeff` | Coefficient CLMs | `ℕ → (E →L[ℝ] ℝ)` — continuous linear functionals extracting coordinates |
| `expansion` | Expansion identity | For every scalar CLF `φ` and `f ∈ E`: `φ(f) = ∑_m c_m(f) · φ(ψ_m)` |
| `basis_growth` | Polynomial growth | Each seminorm of each basis element grows at most polynomially in `m` |
| `coeff_decay` | Super-polynomial decay | Coefficients decay faster than any polynomial, controlled by a single seminorm |

### Example: Schwartz space (current instance)

The library provides `NuclearSpace (SchwartzMap D ℝ)` in `Axioms.lean` via a single axiom:

```lean
axiom schwartz_nuclearSpace
    (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ)

instance (D : Type*) [...] : NuclearSpace (SchwartzMap D ℝ) :=
  schwartz_nuclearSpace D
```

The axiom encodes the classical Dynin-Mityagin theorem (nuclearity of Schwartz space via the Hermite function expansion), which is not yet fully formalized in Mathlib.

### Which spaces are nuclear?

The test function space $E$ **must** be nuclear Fréchet for the construction to
apply. Not every function space qualifies. A theorem of Grothendieck: an
infinite-dimensional Banach (or Hilbert) space is never nuclear. Nuclearity
requires the topology to be strictly weaker than any single norm — it needs
a *family* of seminorms with specific decay properties between them.

| Space | Nuclear? | Why |
|---|---|---|
| $C^\infty(M)$, $M$ compact | Yes | Projective limit of Sobolev spaces; linking maps are nuclear |
| $\mathcal{S}(\mathbb{R}^d)$ | Yes | Same structure with Hermite eigenbasis |
| $s(\mathbb{Z}^d)$ (rapidly decaying sequences) | Yes | Discrete analogue of Schwartz space |
| $H^s(M)$ for fixed $s$ | **No** | Hilbert space, infinite-dimensional |
| $\ell^2(\mathbb{Z}^d)$ | **No** | Hilbert space, infinite-dimensional |
| $L^2(\mathbb{R}^d)$ | **No** | Hilbert space, infinite-dimensional |
| $\mathbb{R}^N$ (finite lattice) | Yes | Finite-dimensional (trivially nuclear) |

The pattern: $C^\infty = \bigcap_k H^k$ is nuclear (intersection of all Sobolev
levels), but any individual $H^k$ is not. The Gaussian measure lives on the dual
$\mathcal{D}' = \bigcup_k H^{-k}$ (distributions), which contains every $H^{-k}$.

### Target instances for other spaces

**$C^\infty(S^1)$ via Fourier basis.** Basis: Fourier modes $e^{inx}$. Seminorms: Sobolev norms $\|f\|_k = \sum_n (1+|n|)^{2k} |\hat{f}(n)|^2$. Growth: $\|e^{inx}\|_k = (1+|n|)^k$. Decay: $|\hat{f}(n)| \cdot (1+|n|)^k \le C \|f\|_{k+1}$.

**$C^\infty(M)$ for compact Riemannian $M$.** Basis: eigenfunctions of the Laplace-Beltrami operator. Growth from Weyl asymptotics: eigenvalue growth $\sim n^{2/\dim M}$. Decay from smoothness.

**Finite lattice spaces $\Lambda \to \mathbb{R}$.** Finite-dimensional spaces are trivially nuclear. Standard basis; growth/decay are trivial since finitely many terms are nonzero.

**Infinite lattice $\mathbb{Z}^d$: rapidly decaying sequences $s(\mathbb{Z}^d)$.** The space $\ell^2(\mathbb{Z}^d)$ is a Hilbert space and therefore **not** nuclear. To get a nuclear space on an infinite lattice, use $s(\mathbb{Z}^d)$ — sequences $f : \mathbb{Z}^d \to \mathbb{R}$ satisfying $\sum_n |f(n)|^2 (1+|n|)^{2k} < \infty$ for all $k$. This is the discrete analogue of Schwartz space. Basis: standard delta functions $e_n$. Coefficients: point evaluations $f \mapsto f(n)$. Growth: $p_k(e_n) = (1+|n|)^k$. Decay: $|f(n)| (1+|n|)^k \le p_k(f)$. No axioms needed — all proofs are elementary. This is the easiest infinite-dimensional instance to formalize.

**Half-line via Laguerre basis.** Laguerre functions on $\mathbb{R}_+$ play the role of Hermite functions on $\mathbb{R}$. Growth and decay estimates map 1:1 to the Hermite case.

**Tensor products via Köthe sequences.** Given `NuclearSpace E` and `NuclearSpace F`, the tensor product basis is $\{\psi_i \otimes \varphi_j\}$ indexed by $\mathbb{N} \times \mathbb{N}$ (Cantor pairing to $\mathbb{N}$). Product weights give polynomial growth; product decays give super-polynomial decay.

## End-to-end workflow: from spaces to measures

The library has three layers. Layer 1 (test function spaces) and Layer 2
(covariance operators) are supplied by the user; Layer 3 (the measure and
all its properties) is produced automatically by the library.

```
Layer 1: Test function space E          [user provides NuclearSpace instance]
Layer 2: Covariance operator T : E → H  [user constructs, typically via heat kernel]
Layer 3: measure T, charFun, moments    [library produces automatically]
```

### Layer 1: Define the test function space

Each space needs a `NuclearSpace` instance. The instance specifies the
topology (via seminorms) and the Schauder basis used internally by the
construction. **The choice of basis does not affect the resulting measure** —
it only affects the internal proof machinery.

#### Schwartz space $\mathcal{S}(\mathbb{R}^d)$ (implemented)

```lean
-- Already provided in Axioms.lean (as an axiom)
instance : NuclearSpace (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ) :=
  schwartz_nuclearSpace _
```

#### Circle $S^1$ of circumference $L$ (planned)

```lean
-- Smooth functions on the circle ℝ/Lℤ
abbrev SmoothCircle (L : ℝ) [Fact (0 < L)] := ...

instance : NuclearSpace (SmoothCircle L) where
  ι := ℕ                            -- single Sobolev index k
  p := sobolevSeminorm L             -- ‖f‖_k² = Σ_n (1+|n|)^{2k} |f̂_n|²
  basis := fourierBasis L             -- e^{2πinx/L} reindexed to ℕ
  coeff := fourierCoeff L             -- Fourier coefficients
  ...

-- Laplacian eigenvalues: λ_n = (2πn/L)² for the n-th Fourier mode
-- Circumference L is a parameter: it determines the eigenvalue spacing
```

#### Finite periodic lattice with $N$ sites (planned)

```lean
-- N equally spaced points on a circle, with periodic boundary conditions
-- As a vector space this is just ℝ^N; periodicity enters through the Laplacian
abbrev PeriodicLattice (N : ℕ) := Fin N → ℝ

instance : NuclearSpace (PeriodicLattice N) where
  ι := Unit                          -- single norm (finite-dim)
  basis := fun k => Pi.single k 1    -- standard basis
  ...                                -- trivial: finite-dim spaces are nuclear

-- Laplacian eigenvalues: λ_k = (2N/L)² sin²(πk/N) for spacing a = L/N
-- Lattice spacing a (or equivalently L and N) is NOT part of the
-- NuclearSpace instance — it parameterizes the Laplacian operator
```

#### Tensor products (planned)

```lean
-- Generic: given NuclearSpace E₁ and NuclearSpace E₂, build E₁ ⊗̂ E₂
-- Defined as a Köthe sequence space — no abstract tensor product theory needed
structure NuclearTensorProduct (E₁ E₂ : Type*) [NuclearSpace E₁] [NuclearSpace E₂] := ...

instance : NuclearSpace (NuclearTensorProduct E₁ E₂) where
  ι := ι₁ × ι₂                      -- product seminorm index
  basis := fun m =>                   -- product basis via Cantor pairing
    let (i,j) := Nat.unpair m
    basis₁ i ⊗ basis₂ j
  ...

-- Specific product spaces are abbreviations:
abbrev Torus2 (L₁ L₂) := NuclearTensorProduct (SmoothCircle L₁) (SmoothCircle L₂)
abbrev Cylinder (L) := NuclearTensorProduct (SmoothCircle L) (SchwartzMap ℝ¹ ℝ)
```

### Layer 2: Build the covariance operator $T$

The operator $T : E \to H$ determines the specific Gaussian measure —
its covariance, its support properties, its physical interpretation.
The library doesn't prescribe how $T$ is built; it accepts any CLM.

In QFT, $T$ is typically a function of the Laplacian: $T = f(-\Delta + m^2)$,
most commonly $f(x) = x^{-1/2}$ for the Gaussian free field.

#### The heat kernel as the fundamental building block

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

#### Heat kernels on each space

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

#### Constructing $T$ on a product space

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

### Layer 3: The library produces the measure

Once you have `[NuclearSpace E]` and `T : E →L[ℝ] H`, everything else is automatic:

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
```

### Full example: lattice GFF on a 2-torus

Putting all three layers together for the massive Gaussian free field
on a $2$-torus with side lengths $L_1, L_2$ and lattice spacings
$a_i = L_i / N_i$:

```lean
variable (L₁ L₂ : ℝ) [Fact (0 < L₁)] [Fact (0 < L₂)]
variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂]
variable (mass s : ℝ) (hs : 0 < s)

-- Layer 1: test function space = ℝ^{N₁ × N₂}  (trivially nuclear)
abbrev E := Fin N₁ × Fin N₂ → ℝ
instance : NuclearSpace E := ...

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

### Continuum limit

To take the continuum limit $a \to 0$ (i.e., $N \to \infty$ with $L$ fixed),
the characteristic functional identity reduces the problem to:

$$\|T_N(r_N f)\|^2 \to \|T(f)\|^2 \qquad \forall f \in E_{\text{continuum}}$$

where $r_N : E_{\text{continuum}} \to E_N$ restricts a smooth function to lattice
points. See [lattice-continuum limit](docs/lattice-continuum-limit.md) for details.

## Module structure

```
GaussianField/
  NuclearSpace.lean            -- NuclearSpace typeclass + expansion_H lemma
  Axioms.lean                  -- Schwartz nuclearity axiom → instance
  SpectralTheorem.lean         -- Compact self-adjoint spectral theorem
  NuclearSVD.lean              -- SVD for nuclear operators
  NuclearFactorization.lean    -- Source-indexed nuclear representation
  TargetFactorization.lean     -- Target-indexed factorization with ONB
  SeriesConvergence.lean       -- Gaussian series convergence (Tonelli)
  Construction.lean            -- Main construction + characteristic functional
  Properties.lean              -- Gaussianity, moments, Lp integrability

SchwartzNuclear/               -- Partial proof of Schwartz nuclearity (WIP)
  HermiteFunctions.lean        -- Hermite functions ψ_n as Schwartz maps
  SchwartzHermiteExpansion.lean -- 1D Hermite expansion, eigenvalue decay
  Basis1D.lean                 -- 1D Hermite basis + completeness
  SchwartzSlicing.lean         -- Fubini slicing for partial Hermite coefficients
  HermiteTensorProduct.lean    -- Multi-d Hermite expansion + NuclearSpace instance
```

### Dependency chain

```
NuclearSpace  →  Axioms (Schwartz instance)
     ↓
NuclearFactorization
     ↓
SpectralTheorem  →  NuclearSVD  →  TargetFactorization
                                        ↓
                                  SeriesConvergence
                                        ↓
                                    Construction
                                        ↓
                                    Properties
```

## Axiom budget

The library assumes **1 axiom**: that Schwartz space is a nuclear space. This is stated in `Axioms.lean`:

```lean
axiom schwartz_nuclearSpace
    (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ)
```

The core construction (everything downstream of `NuclearSpace.lean`) uses **no custom axioms** — it works for any type carrying a `NuclearSpace` instance.

### Why an axiom?

Nuclearity of Schwartz space is a classical result (Dynin-Mityagin, 1960) proved via the Hermite function expansion. The `SchwartzNuclear/` directory contains ~6,500 lines of Lean 4 toward eliminating this axiom, reducing it to 1 analytical axiom (seminorm control of partial Hermite coefficients) and 3 sorrys (Fubini for EuclideanSpace, smoothness/decay of partial coefficients). See the [SchwartzNuclear README](SchwartzNuclear/README.md) for details.

Providing a `NuclearSpace` instance for a different space (e.g., $C^\infty(S^1)$) would require its own analogous proof (or axiom).

## Further documentation

- [Concrete instances](docs/concrete-instances.md) — `NuclearSpace` instances for $C^\infty(S^1_L)$, finite lattices, periodic lattices, and generic tensor products, with Lean sketches
- [Operator construction](docs/operator-construction.md) — building covariance operators on product spaces via the heat kernel $e^{-s\Delta}$, Mathlib support, and the factorization theorem
- [Lattice-continuum limit](docs/lattice-continuum-limit.md) — convergence of lattice Gaussian measures to continuum measures via characteristic functionals
- [Generalization plan](docs/generalization-plan.md) — architecture of the `NuclearSpace` typeclass, design decisions, and roadmap for future instances

## Future work

- **New instances**: $C^\infty(S^1)$, $C^\infty(M)$ for compact $M$, lattice spaces, half-spaces, tensor products (see [concrete instances](docs/concrete-instances.md))
- **Heat kernel toolkit**: Formalize the discrete Laplacian, heat kernel, and Kronecker factorization theorem (see [operator construction](docs/operator-construction.md))
- **Lattice-continuum limits**: Formalize convergence via characteristic functionals (see [lattice-continuum limit](docs/lattice-continuum-limit.md))
- **Support theorems / Besov regularity**: The `pairing_memLp` result (Fernique-type $L^p$ bounds) is the first step toward showing $\mu$-a.s. $\omega \in B^s_{p,q}$ for appropriate $s, p, q$
- **$\sigma$-algebra coincidence**: For separable nuclear Fréchet spaces, the cylindrical and Borel $\sigma$-algebras on the dual coincide

## Building

```bash
lake update
lake build
```

Requires Lean 4 v4.28.0-rc1 and Mathlib (fetched automatically by Lake).

## License

Apache 2.0

## References

- I.M. Gel'fand and N.Ya. Vilenkin, *Generalized Functions*, Vol. 4 (1964)
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974)
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- S. Thangavelu, *Lectures on Hermite and Laguerre Expansions* (1993)
- A. Dynin, B. Mityagin, "Criterion for nuclearity in terms of approximative dimension" (1960)
