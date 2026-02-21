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

The core abstraction is the `DyninMityaginSpace` typeclass, which encodes the Dynin-Mityagin structure: a nuclear Fréchet space with a countable Schauder basis admitting polynomial growth and super-polynomial decay estimates.

```lean
class DyninMityaginSpace (E : Type*)
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
- **Bundled seminorms.** The `ι` and `p` are fields, not class parameters, so `[DyninMityaginSpace E]` works in theorem signatures without specifying the seminorm family.
- **Scalar expansion.** The expansion axiom tests against `φ : E →L[ℝ] ℝ`, not arbitrary Hilbert spaces. This avoids universe polymorphism issues. The Hilbert-space form is recovered as the 3-line lemma `DyninMityaginSpace.expansion_H`.
- **ℕ exponents.** Polynomial bounds use `k : ℕ` and `pow`, avoiding `Real.rpow` pain.

## Providing a `DyninMityaginSpace` instance for a new space

To use this library with a function space other than Schwartz space, provide a `DyninMityaginSpace` instance. Here is what you need:

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

The library provides a fully proved instance in `SchwartzNuclear/HermiteNuclear.lean`:

```lean
noncomputable instance schwartz_dyninMityaginSpace [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D ℝ
  basis m := (schwartzRapidDecayEquiv D).symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp (schwartzRapidDecayEquiv D).toContinuousLinearMap
  expansion := schwartz_expansion_from_equiv (schwartzRapidDecayEquiv D)
  basis_growth := schwartz_basis_growth_from_equiv (schwartzRapidDecayEquiv D)
  coeff_decay := schwartz_coeff_decay_from_equiv (schwartzRapidDecayEquiv D)
```

This is the Dynin-Mityagin theorem: nuclearity of Schwartz space via the Hermite function expansion and the isomorphism $\mathcal{S}(\mathbb{R}^d) \cong s(\mathbb{N})$.

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

**Tensor products via Kothe sequences (implemented).** Given `DyninMityaginSpace E` and `DyninMityaginSpace F`, the tensor product `NuclearTensorProduct E F` is realized as `RapidDecaySeq` with basis indices encoded via Cantor pairing $\mathbb{N}^2 \to \mathbb{N}$. The pure tensor embedding `pure e₁ e₂` is proved bilinear (`pureLin`) and jointly continuous (`pure_continuous`), with the seminorm bound factoring through the Cantor pairing arithmetic.

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
| [NuclearSpace.lean](Nuclear/NuclearSpace.lean) | 358 | `NuclearSpace` typeclass (Pietsch), Hahn-Banach for seminorms, DM -> Pietsch implication |
| [NuclearTensorProduct.lean](Nuclear/NuclearTensorProduct.lean) | 831 | `RapidDecaySeq`, `rapidDecaySeminorm`, Cantor pairing, `NuclearTensorProduct`, `pure` (bilinear, jointly continuous) |

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
SchwartzNuclear/   GaussianField/
  ...              NuclearFactorization
  HermiteNuclear        ↓
       ↓          SpectralTheorem → NuclearSVD → TargetFactorization
       ↓                                              ↓
       └──────────────→ GaussianField.lean ←──── Construction
                                                      ↓
                                                  Properties
                                                      ↓
                                                  IsGaussian
```

## Axiom budget

**0 custom axioms.** The Schwartz nuclearity instance `DyninMityaginSpace (SchwartzMap D ℝ)` is fully proved in `SchwartzNuclear/` (~7,700 lines) via the Hermite function expansion and the Dynin-Mityagin isomorphism. See the [Schwartz nuclearity proof](docs/schwartz-nuclearity-proof.md) for details.

An axiom fallback is available as an inactive comment in `GaussianField.lean` for faster builds during development.

## Further documentation

- [Workflow](docs/workflow.md) — end-to-end three-layer workflow with Lean code examples
- [Nuclear space infrastructure](docs/nuclear-space-infrastructure.md) — the `DyninMityaginSpace` typeclass, `RapidDecaySeq`, and why nuclearity is needed
- [Schwartz nuclearity proof](docs/schwartz-nuclearity-proof.md) — the 7,700-line proof that Schwartz space is nuclear
- [Gaussian field construction](docs/gaussian-field-construction.md) — the 2,960-line measure construction
- [Concrete instances](docs/concrete-instances.md) — `DyninMityaginSpace` instances for $C^\infty(S^1_L)$, finite lattices, periodic lattices, and generic tensor products, with Lean sketches
- [Operator construction](docs/operator-construction.md) — building covariance operators on product spaces via the heat kernel $e^{-s\Delta}$, Mathlib support, and the factorization theorem
- [Lattice-continuum limit](docs/lattice-continuum-limit.md) — convergence of lattice Gaussian measures to continuum measures via characteristic functionals
- [Generalization plan](docs/generalization-plan.md) — architecture of the `DyninMityaginSpace` typeclass, design decisions, and roadmap for future instances

## Future work

- **New instances**: $C^\infty(S^1)$, $C^\infty(M)$ for compact $M$, lattice spaces, half-spaces (see [concrete instances](docs/concrete-instances.md))
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
