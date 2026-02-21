# The `DyninMityaginSpace` typeclass

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

## Key design decisions

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

## Which spaces are nuclear?

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

## Target instances for other spaces

**$C^\infty(S^1)$ via Fourier basis.** Basis: Fourier modes $e^{inx}$. Seminorms: Sobolev norms $\|f\|_k = \sum_n (1+|n|)^{2k} |\hat{f}(n)|^2$. Growth: $\|e^{inx}\|_k = (1+|n|)^k$. Decay: $|\hat{f}(n)| \cdot (1+|n|)^k \le C \|f\|_{k+1}$.

**$C^\infty(M)$ for compact Riemannian $M$.** Basis: eigenfunctions of the Laplace-Beltrami operator. Growth from Weyl asymptotics: eigenvalue growth $\sim n^{2/\dim M}$. Decay from smoothness.

**Finite lattice spaces $\Lambda \to \mathbb{R}$.** Finite-dimensional spaces are trivially nuclear. Standard basis; growth/decay are trivial since finitely many terms are nonzero.

**Infinite lattice $\mathbb{Z}^d$: rapidly decaying sequences $s(\mathbb{Z}^d)$.** The space $\ell^2(\mathbb{Z}^d)$ is a Hilbert space and therefore **not** nuclear. To get a nuclear space on an infinite lattice, use $s(\mathbb{Z}^d)$ — sequences $f : \mathbb{Z}^d \to \mathbb{R}$ satisfying $\sum_n |f(n)|^2 (1+|n|)^{2k} < \infty$ for all $k$. This is the discrete analogue of Schwartz space. Basis: standard delta functions $e_n$. Coefficients: point evaluations $f \mapsto f(n)$. Growth: $p_k(e_n) = (1+|n|)^k$. Decay: $|f(n)| (1+|n|)^k \le p_k(f)$. No axioms needed — all proofs are elementary. This is the easiest infinite-dimensional instance to formalize.

**Half-line via Laguerre basis.** Laguerre functions on $\mathbb{R}_+$ play the role of Hermite functions on $\mathbb{R}$. Growth and decay estimates map 1:1 to the Hermite case.

**Tensor products via Kothe sequences (implemented).** Given `DyninMityaginSpace E` and `DyninMityaginSpace F`, the tensor product `NuclearTensorProduct E F` is realized as `RapidDecaySeq` with basis indices encoded via Cantor pairing $\mathbb{N}^2 \to \mathbb{N}$. The pure tensor embedding `pure e₁ e₂` is proved bilinear (`pureLin`) and jointly continuous (`pure_continuous`), with the seminorm bound factoring through the Cantor pairing arithmetic.
