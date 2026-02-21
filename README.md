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
- A nuclear Fréchet space `E` with `[DyninMityaginSpace E]` instance
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
| `measure_isGaussian` | `IsGaussian (measure T)` | Mathlib's `IsGaussian` typeclass instance |

### Design notes

The API takes only `T` as an explicit argument — no proof of infinite-dimensionality
is required. When `H` is finite-dimensional, the construction embeds `H` isometrically
into $\ell^2$ and builds the measure there, yielding a degenerate (finite-rank) Gaussian.
This allows testing with toy cases like $H = \mathbb{R}^n$.

`Configuration E` is defined as `WeakDual ℝ E` — the space of continuous linear functionals on $E$ with the weak-* topology. Elements $\omega \in E'$ are "configurations" or "generalized functions" that pair with test functions: $\omega(f) \in \mathbb{R}$.

## The `DyninMityaginSpace` typeclass

See [docs/dynin-mityagin-typeclass.md](docs/dynin-mityagin-typeclass.md) for the
full typeclass definition, design decisions, how to provide an instance for a new
space, which spaces are nuclear, and target instances (circles, lattices, tensor
products, etc.).

## End-to-end workflow: from spaces to measures

See [docs/workflow.md](docs/workflow.md) for the full three-layer workflow
(test function spaces, covariance operators, measure construction) with
Lean code examples for Schwartz space, circles, lattices, tensor products,
heat kernels, and the lattice-continuum limit.

## Module structure

The project has three libraries, with imports flowing left to right:
`Nuclear` <- `SchwartzNuclear` <- `GaussianField`.

### 1. [Nuclear Space Infrastructure](docs/nuclear-space-infrastructure.md)

The `DyninMityaginSpace` typeclass and the canonical model `RapidDecaySeq` (the Kothe
sequence space $s(\mathbb{N})$), shared by both `SchwartzNuclear/` and
`GaussianField/`.

| File | Lines | Contents |
|------|------:|----------|
| [DyninMityagin.lean](Nuclear/DyninMityagin.lean) | 76 | `DyninMityaginSpace` typeclass (Dynin-Mityagin), `expansion_H` lemma |
| [NuclearSpace.lean](Nuclear/NuclearSpace.lean) | 487 | `NuclearSpace` typeclass (Pietsch), Hahn-Banach for seminorms, `hasSum_basis` (strong Schauder convergence), DM -> Pietsch |
| [NuclearTensorProduct.lean](Nuclear/NuclearTensorProduct.lean) | 1,125 | `RapidDecaySeq`, `NuclearTensorProduct`, `pure`, universal property (`lift`, `lift_pure`) |

#### Two definitions of nuclearity

The library contains two characterizations of nuclear spaces:

1. **Dynin-Mityagin** (`DyninMityaginSpace` in [DyninMityagin.lean](Nuclear/DyninMityagin.lean)) —
   A nuclear Fréchet space with a countable Schauder basis admitting polynomial
   growth of seminorms and super-polynomial decay of coefficients. This is the
   operational definition used by the Gaussian measure construction.

2. **Pietsch** (`NuclearSpace` in [NuclearSpace.lean](Nuclear/NuclearSpace.lean)) —
   For every continuous seminorm $p$, there exists a dominating seminorm $q \ge p$
   such that the canonical map $E_q \to E_p$ is nuclear (expressible as
   $p(x) \le \sum_n c_n |f_n(x)|$ with $\sum c_n < \infty$ and $|f_n| \le q$).
   This is the standard textbook definition (Pietsch, Grothendieck).

The Dynin-Mityagin characterization is strictly stronger: it additionally requires
the existence of a Schauder basis. The implication
`DyninMityaginSpace.toNuclearSpace` (DM -> Pietsch) is proved in
[NuclearSpace.lean](Nuclear/NuclearSpace.lean). The converse holds for
nuclear Fréchet spaces that already possess a Schauder basis (the
Dynin-Mityagin theorem), but is not formalized since our applications
(Schwartz spaces) obtain the DM structure directly from the Hermite basis.

#### Tensor products of nuclear spaces

`NuclearTensorProduct E₁ E₂` is the completed nuclear tensor product of two
`DyninMityaginSpace` spaces. It carries a `DyninMityaginSpace` instance
(hence is itself nuclear) and satisfies the **universal property**: every
seminorm-bounded bilinear map factors uniquely through the canonical embedding.

**Structural results:**

| Definition / Theorem | Type | Description |
|---|---|---|
| `NuclearTensorProduct.assoc` | `(E₁ ⊗̂ E₂) ⊗̂ E₃ ≃L[ℝ] E₁ ⊗̂ (E₂ ⊗̂ E₃)` | Associativity |
| `lift B` | `E₁ ⊗̂ E₂ →L[ℝ] G` | Universal property: factors bilinear maps through `pure` |
| `lift_pure` | `lift B (pure e₁ e₂) = B e₁ e₂` | Factoring identity |

**Schwartz space isomorphisms** (in `SchwartzNuclear/SchwartzTensorProduct.lean`):

| Definition / Theorem | Type | Description |
|---|---|---|
| `schwartzPeelOff d` | `S(ℝ^{d+2}) ≃L S(ℝ^{d+1}) ⊗̂ S(ℝ)` | Peel off one dimension |
| `schwartzTensorEquiv m n` | `S(ℝ^{m+1}) ⊗̂ S(ℝ^{n+1}) ≃L S(ℝ^{m+n+2})` | General tensor-product isomorphism |
| `schwartzPeelOff_pure` | canonicity | Inverse sends `f ⊗ g` to pointwise product |

These isomorphisms identify the tensor product of Schwartz spaces on lower-dimensional
Euclidean spaces with Schwartz space on the product space — the Schwartz kernel theorem.

For the concrete construction (Cantor pairing, `pure`, `lift`, reindexing), see
[docs/tensor-products.md](docs/tensor-products.md). For the roadmap to connect
to Mathlib's abstract `TensorProduct`, see
[docs/abstract-tensor-product-plan.md](docs/abstract-tensor-product-plan.md).

### 2. [Schwartz Space Nuclearity](docs/schwartz-nuclearity-proof.md)

Proves `DyninMityaginSpace (SchwartzMap D ℝ)` for any finite-dimensional $D$ via the
Hermite function expansion and the Dynin-Mityagin isomorphism
$\mathcal{S}(\mathbb{R}^d) \cong s(\mathbb{N})$.

| File | Lines | Contents |
|------|------:|----------|
| [HermiteFunctions.lean](SchwartzNuclear/HermiteFunctions.lean) | 1,853 | 1D Hermite functions, orthonormality, completeness |
| [SchwartzHermiteExpansion.lean](SchwartzNuclear/SchwartzHermiteExpansion.lean) | 1,446 | 1D Schwartz-Hermite expansion, coefficient decay |
| [Basis1D.lean](SchwartzNuclear/Basis1D.lean) | 157 | 1D DyninMityaginSpace fields assembly |
| [ParametricCalculus.lean](SchwartzNuclear/ParametricCalculus.lean) | 316 | Differentiation under the integral sign |
| [SchwartzSlicing.lean](SchwartzNuclear/SchwartzSlicing.lean) | 1,134 | Multi-d slicing and partial Hermite coefficients |
| [HermiteTensorProduct.lean](SchwartzNuclear/HermiteTensorProduct.lean) | 2,619 | Multi-d isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq` |
| [HermiteNuclear.lean](SchwartzNuclear/HermiteNuclear.lean) | 174 | `DyninMityaginSpace` instance from the isomorphism |
| [SchwartzTensorProduct.lean](SchwartzNuclear/SchwartzTensorProduct.lean) | 363 | Tensor product associativity, `schwartzPeelOff`, `schwartzTensorEquiv` |

### 2b. [Circle Nuclearity](docs/concrete-instances.md#1-the-circle-s1_l-of-circumference-l)

Proves `DyninMityaginSpace (SmoothCircle L)` for smooth L-periodic functions
on the circle via the real Fourier basis and the isomorphism
`SmoothCircle L ≃L[ℝ] RapidDecaySeq`.

| File | Lines | Contents |
|------|------:|----------|
| [SmoothCircle/Basic.lean](SmoothCircle/Basic.lean) | ~400 | Type, seminorms, Fourier basis, coefficients |
| [SmoothCircle/Nuclear.lean](SmoothCircle/Nuclear.lean) | ~200 | Decay, CLE, `DyninMityaginSpace` instance |
| [SmoothCircle/Test.lean](SmoothCircle/Test.lean) | ~55 | End-to-end test: Gaussian measure on C∞(S¹) and cylinder S¹×ℝ |

This enables Gaussian fields on the torus T¹ = ℝ/Lℤ and (via tensor products)
on cylinders S¹×ℝ and higher tori Tᵈ. The test file verifies the full pipeline
for both `SmoothCircle L` and the cylinder `NuclearTensorProduct (SmoothCircle L) (SchwartzMap ℝ ℝ)`.
See [concrete instances](docs/concrete-instances.md) for the mathematical details.

**Design note:** `SmoothCircle L` represents smooth L-periodic functions as
`{f : ℝ → ℝ | Periodic f L ∧ ContDiff ℝ ⊤ f}`, avoiding manifold machinery.
Mathlib's `AddCircle L` (= $\mathbb{R}/L\mathbb{Z}$) has rich Fourier analysis
but currently lacks `ChartedSpace`/`SmoothManifoldWithCorners` instances, so
`ContMDiffMap (AddCircle L) F` cannot yet be defined. Once Mathlib gains manifold
structure on `AddCircle`, the type could be refactored to `ContMDiffMap (AddCircle L) F`
and generalized to vector-valued codomain $F$.

### 3. [Gaussian Field Construction](docs/gaussian-field-construction.md)

Given `[DyninMityaginSpace E]` and `T : E →L[ℝ] H`, constructs the centered Gaussian
probability measure on $E' = \text{WeakDual}\ \mathbb{R}\ E$.

| File | Lines | Contents |
|------|------:|----------|
| [SpectralTheorem.lean](GaussianField/SpectralTheorem.lean) | 468 | Compact self-adjoint spectral theorem |
| [NuclearSVD.lean](GaussianField/NuclearSVD.lean) | 640 | SVD for nuclear operators |
| [NuclearFactorization.lean](GaussianField/NuclearFactorization.lean) | 190 | Source-indexed nuclear representation |
| [TargetFactorization.lean](GaussianField/TargetFactorization.lean) | 324 | Target-indexed factorization with ONB |
| [Construction.lean](GaussianField/Construction.lean) | 715 | Main construction + characteristic functional |
| [Properties.lean](GaussianField/Properties.lean) | 193 | Gaussianity, moments, $L^p$ integrability |
| [IsGaussian.lean](GaussianField/IsGaussian.lean) | 160 | Mathlib `IsGaussian` instance for `measure T` |

### Dependency graph

```
Nuclear/
  DyninMityagin → NuclearTensorProduct
       ↓                ↓
SchwartzNuclear/   SmoothCircle/         GaussianField/
  ...              Basic → Nuclear       NuclearFactorization
  HermiteNuclear        ↓                     ↓
       ↓           Test (uses GF)   SpectralTheorem → NuclearSVD → TargetFactorization
  SchwartzTensorProduct                                                ↓
       ↓                                                               ↓
       └──────────────→ GaussianField.lean ←─────────────────── Construction
                                                                       ↓
                                                                   Properties
                                                                       ↓
                                                                   IsGaussian
```

## Axiom budget

**0 custom axioms.** The Schwartz nuclearity instance `DyninMityaginSpace (SchwartzMap D ℝ)` is fully proved in `SchwartzNuclear/` (~7,700 lines) via the Hermite function expansion and the Dynin-Mityagin isomorphism. See the [Schwartz nuclearity proof](docs/schwartz-nuclearity-proof.md) for details.

An axiom fallback is available as an inactive comment in `GaussianField.lean` for faster builds during development.

## Further documentation

- [DyninMityaginSpace typeclass](docs/dynin-mityagin-typeclass.md) — typeclass definition, design decisions, how to construct instances, which spaces are nuclear
- [Workflow](docs/workflow.md) — end-to-end three-layer workflow with Lean code examples
- [Nuclear space infrastructure](docs/nuclear-space-infrastructure.md) — the `NuclearSpace` and `DyninMityaginSpace` typeclasses, `RapidDecaySeq`, and why nuclearity is needed
- [Schwartz nuclearity proof](docs/schwartz-nuclearity-proof.md) — the 7,700-line proof that Schwartz space is nuclear
- [Gaussian field construction](docs/gaussian-field-construction.md) — the 2,960-line measure construction
- [Concrete instances](docs/concrete-instances.md) — `DyninMityaginSpace` instances for $C^\infty(S^1_L)$, finite lattices, periodic lattices, and generic tensor products, with Lean sketches
- [Operator construction](docs/operator-construction.md) — building covariance operators on product spaces via the heat kernel $e^{-s\Delta}$, Mathlib support, and the factorization theorem
- [Lattice-continuum limit](docs/lattice-continuum-limit.md) — convergence of lattice Gaussian measures to continuum measures via characteristic functionals
- [Generalization plan](docs/generalization-plan.md) — architecture of the `DyninMityaginSpace` typeclass, design decisions, and roadmap for future instances
- [Tensor products](docs/tensor-products.md) — concrete construction of `NuclearTensorProduct` via `RapidDecaySeq` and Cantor pairing, `pure`/`lift` API, reindexing, and Schwartz tensor product isomorphisms
- [Abstract tensor product plan](docs/abstract-tensor-product-plan.md) — roadmap for building completed projective tensor products on Mathlib's `TensorProduct`, proving isomorphism with `RapidDecaySeq`, and the nuclear coincidence theorem

## Future work

- **New instances**: $C^\infty(S^1)$ is implemented (with analytical sorrys); remaining targets: $C^\infty(M)$ for compact $M$, lattice spaces, half-spaces (see [concrete instances](docs/concrete-instances.md))
- **Vector-valued generalization**: Generalize `SmoothCircle L` and `SchwartzMap D ℝ` to vector-valued codomains $F$, with nuclearity via $C^\infty(M, \mathbb{R}^n) \cong C^\infty(M, \mathbb{R})^n \cong s(\mathbb{N})$; long-term, refactor to `ContMDiffMap (AddCircle L) F` once Mathlib gains manifold structure on `AddCircle`
- **Heat kernel toolkit**: Formalize the discrete Laplacian, heat kernel, and Kronecker factorization theorem (see [operator construction](docs/operator-construction.md))
- **Lattice-continuum limits**: Formalize convergence via characteristic functionals (see [lattice-continuum limit](docs/lattice-continuum-limit.md))
- **Abstract tensor product**: Build completed projective tensor products on Mathlib's algebraic `TensorProduct`, prove isomorphism with `RapidDecaySeq` for DM spaces, and the nuclear coincidence theorem $\pi = \varepsilon$ (see [abstract tensor product plan](docs/abstract-tensor-product-plan.md))
- **Support theorems / Besov regularity**: The `pairing_memLp` result (Fernique-type $L^p$ bounds) is the first step toward showing $\mu$-a.s. $\omega \in B^s_{p,q}$ for appropriate $s, p, q$
- **$\sigma$-algebra coincidence**: For separable nuclear Fréchet spaces, the cylindrical and Borel $\sigma$-algebras on the dual coincide

## Building

```bash
lake update
lake build
```

Requires Lean 4 v4.28.0-rc1 and Mathlib (fetched automatically by Lake).

## Author

Michael R. Douglas

## License

Apache 2.0

## References

- I.M. Gel'fand and N.Ya. Vilenkin, *Generalized Functions*, Vol. 4 (1964)
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974)
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- S. Thangavelu, *Lectures on Hermite and Laguerre Expansions* (1993)
- A. Dynin, B. Mityagin, "Criterion for nuclearity in terms of approximative dimension" (1960)
