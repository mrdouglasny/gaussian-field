# Generalization Plan: Beyond Schwartz Spaces

## Goal

Generalize the Gaussian measure construction from `SchwartzMap D F` to arbitrary
nuclear Frechet spaces, enabling measures on function spaces over compact
manifolds, lattices, half-spaces, and tensor products of these.

## Current State

**Phase 1 is complete.** The construction is fully generalized to arbitrary
`NuclearSpace E`. The only Schwartz-specific content is the instance in
`Axioms.lean`, which provides `NuclearSpace (SchwartzMap D F)` via 5 axioms.

All files from `NuclearSpace.lean` through `Properties.lean` are parametric
over `E` with `[NuclearSpace E]`. New instances for other function spaces
can be added by providing the typeclass fields (see README).

## Mathematical Foundation

The typeclass formalizes the **Dynin-Mityagin theorem**: every nuclear Frechet
space with a Schauder basis is isomorphic to a Kothe sequence space with
rapidly decaying weights. This avoids the abstract Grothendieck definition
of nuclear spaces (bornologies, topological tensor products, Pietsch
domination) in favor of sequences, series, and algebraic bounds — exactly
what Lean 4 handles best.

## Architecture

### The NuclearSpace typeclass

Frechet spaces are not normable, so we use Mathlib's locally convex TVS
mixins rather than `NormedAddCommGroup` / `NormedSpace`. The seminorm
family is bundled inside the class (not a parameter) so that Lean's
typeclass synthesis can infer everything from `E` alone. The expansion
axiom tests against an arbitrary continuous linear functional `φ : E →L[R] R`
rather than quantifying over Hilbert spaces, since any `⟪w, T(-)⟫` is
such a functional. Exponents use `ℕ` to avoid `rpow` pain.

```lean
class NuclearSpace (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E] where
  ι : Type*
  p : ι → Seminorm ℝ E
  h_with : WithSeminorms p
  basis : ℕ → E
  coeff : ℕ → (E →L[ℝ] ℝ)
  expansion :
    ∀ (φ : E →L[ℝ] ℝ) (f : E), φ f = ∑' m, (coeff m f) * φ (basis m)
  basis_growth :
    ∀ (i : ι), ∃ C > 0, ∃ (s : ℕ),
    ∀ m, p i (basis m) ≤ C * (1 + (m : ℝ)) ^ s
  coeff_decay :
    ∀ (k : ℕ), ∃ C > 0, ∃ (q : ι),
    ∀ f m, |coeff m f| * (1 + (m : ℝ)) ^ k ≤ C * p q f
```

### Design decisions

**Locally convex mixins, not NormedSpace.** `SchwartzMap D F` is a Frechet
space — it is not normable. Requiring `NormedAddCommGroup` would make the
Schwartz instance impossible. The mixins `[AddCommGroup E] [Module ℝ E]
[TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E]` are
exactly what Mathlib uses for locally convex spaces and what `SchwartzMap`
satisfies.

**Bundled seminorms.** If `ι` and `p` were class parameters rather than
fields, writing `[NuclearSpace E]` in theorem signatures would fail —
Lean cannot guess the seminorm family from `E` alone. Bundling them
ensures typeclass inference works automatically.

**Simplified expansion.** Nuclearity is an intrinsic property of E — it
holds regardless of what Hilbert space E is eventually mapped into.
Quantifying over `∀ {H : Type*} [InnerProductSpace ℝ H] (T : E →L[ℝ] H)`
inside the class forces the definition of E's topology to range over all
Hilbert spaces in all universes, causing `max u v` universe errors and
typeclass inference failures. The scalar form `∀ (φ : E →L[ℝ] ℝ)` is
purely intrinsic to E.

The H-expansion is recovered as a 3-line lemma in NuclearFactorization.lean,
not an axiom in the class:

```lean
lemma expansion_H [NuclearSpace E] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : E →L[ℝ] H) (w : H) (f : E) :
    ⟪w, T f⟫_ℝ = ∑' m, (NuclearSpace.coeff m f) * ⟪w, T (NuclearSpace.basis m)⟫_ℝ := by
  -- f ↦ ⟪w, T f⟫ is a scalar CLF
  let φ : E →L[ℝ] ℝ := (innerSL ℝ w).comp T
  exact NuclearSpace.expansion φ f
```

This cleanly separates concerns: the typeclass knows only about E's
topology, while the Gel'fand triple (E ⊂ H ⊂ E') is formed dynamically
in the factorization and construction files where T is actually provided.

**ℕ exponents.** Using `k : ℝ` would force `Real.rpow`, which in Lean
requires non-negativity proofs at every step and lacks definitional
equalities. Polynomial bounds are perfectly captured by `k : ℕ` and
`Nat.cast` + `pow`, which are much easier to work with.

### Why these fields

| Field | Mathematical role | Used in |
|---|---|---|
| `basis` | Schauder basis {ψ_m} | NuclearFactorization: expansion of T |
| `coeff` | Continuous coefficient functionals {c_m} | NuclearFactorization: nuclear series |
| `expansion` | φ(f) recoverable from coefficients | NuclearFactorization: nuclear representation |
| `basis_growth` | poly growth of seminorms of basis | NuclearFactorization: bounding ‖T(ψ_m)‖ |
| `coeff_decay` | super-poly decay of coefficients | NuclearFactorization: ell1 summability |

### Weighted ell2 embedding

The current code uses `SchwartzMap.mkCLMtoNormedSpace` to build `j : S → ell2`.
The naive replacement `j(f) := (coeff m f)_m` fails the target factorization:
if `T : E →L[ℝ] H` has growth bound `‖T(ψ_m)‖ ≤ C(1+m)^s`, then factoring
T through an unweighted j requires `∑ ‖T(ψ_m)‖^2 < ∞`, which diverges
for polynomial growth.

The fix is a **weighted family** of ell2 embeddings parameterized by a
decay rate k:

```lean
def nuclearEll2Embedding [NuclearSpace E] (k : ℕ) : E →L[ℝ] ell2 :=
  -- maps f ↦ ((1 + m)^k * coeff m f)_{m : ℕ}
```

By `coeff_decay`, for any k there exists a seminorm `p_q` such that
`|(1+m)^k * coeff m f| ≤ C * p_q(f)`, so the sequence is in ell2 for
each f, and the map is continuous from the Frechet topology.

In `TargetFactorization.lean`, given `T : E →L[ℝ] H` with growth bound
`‖T(ψ_m)‖ ≤ C(1+m)^s`, choose the embedding `j_k` with `k > s + 1`.
Then the comparison vectors satisfy:

    ‖v_m‖ ≤ ‖T(ψ_m)‖ / (1+m)^k ≤ C(1+m)^{s-k}

which is summable since `s - k < -1`. The factorization
`⟪e_n, Tf⟫ = ⟪v_n, j_k(f)⟫` succeeds because the super-polynomial
decay of coefficients absorbs any finite weight.

## File-by-file refactor plan

### New file: NuclearSpace.lean

Define the `NuclearSpace` typeclass and the weighted ell2 embedding family.
Place it before Axioms.lean in the import chain.

Contents:
- `NuclearSpace` class definition
- `nuclearEll2Embedding (k : ℕ) : E →L[ℝ] ell2`
- Proof that the embedding is continuous (from `coeff_decay` + `WithSeminorms`)
- Helper lemmas: weight arithmetic, summability criteria

### Axioms.lean

Replace the 5 free-standing axioms with a single axiom-backed instance:

```lean
noncomputable instance schwartz_nuclearSpace :
    NuclearSpace (SchwartzMap D F) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D F
  basis := schwartzHermiteBasis D F       -- axiom
  coeff := schwartzHermiteCoeff D F       -- axiom
  expansion := schwartz_hermite_expansion -- axiom
  basis_growth := schwartz_hermite_seminorm_growth -- axiom
  coeff_decay := schwartz_hermite_coefficient_decay -- axiom
```

The 5 axioms remain (Hermite infrastructure is not in Mathlib) but are
now packaged as proof obligations of the instance rather than floating
declarations. The axiom signatures must be adjusted to match the new
typeclass fields (ℕ exponents, simplified expansion, bundled seminorms).

### NuclearFactorization.lean

Replace all occurrences of `SchwartzMap D F` with a type variable
`E` carrying `[NuclearSpace E]`. The proof structure is identical:

1. `expansion` gives `φ(f) = ∑ c_m(f) * φ(ψ_m)` for any CLF φ
2. For `T : E →L[ℝ] H` and `w : H`, apply expansion to `φ := ⟪w, T(-)⟫`
3. `basis_growth` + `Seminorm.bound_of_continuous` gives poly growth of ‖T(ψ_m)‖
4. `coeff_decay` gives super-poly decay of |c_m(f)|
5. Combining 3 and 4 gives ell1 summability of ‖y_m‖

The renamed theorem:

```lean
theorem nuclear_representation [NuclearSpace E]
    (T : E →L[ℝ] H) :
    ∃ (φ : ℕ → (E →L[ℝ] ℝ)) (y : ℕ → H),
      Summable (fun m => ‖y m‖) ∧
      ∀ f, T f = ∑' m, (φ m f) • (y m)
```

Note: `Seminorm.bound_of_continuous` requires access to `WithSeminorms p`.
This is available via `NuclearSpace.h_with`.

### TargetFactorization.lean

Replace `schwartz_ell2_embedding_from_decay` with the weighted embedding.
The key change: given `T : E →L[ℝ] H` with growth exponent s from
`nuclear_representation`, choose `k := s + 2` and use
`nuclearEll2Embedding k` as the factorization target.

```lean
theorem target_factorization [NuclearSpace E]
    (T : E →L[ℝ] H) :
    ∃ (e : ℕ → H) (K : Type*) [inst : InnerProductSpace ℝ K]
      (j : E →L[ℝ] K) (v : ℕ → K),
      Summable (fun n => ‖v n‖) ∧
      ∀ n f, ⟪e n, T f⟫ = ⟪v n, j f⟫
```

### Construction.lean

Generalize the sample space. The Hilbert space H and covariance operator
T remain the central inputs — they define the Cameron-Martin space and
the specific probability measure. Only the *typeclass* is decoupled
from H; the measure API keeps the full Gel'fand triple E ⊂ H ⊂ E'.

```lean
abbrev Configuration (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [TopologicalAddGroup E] [ContinuousSMul ℝ E] :=
  WeakDual ℝ E

-- H and T define the specific probability measure
def measure [NuclearSpace E] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) : Measure (Configuration E) := ...

-- Covariance is the inner product on the Cameron-Martin space
def covariance [NuclearSpace E] {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : E →L[ℝ] H) (f g : E) : ℝ := ⟪T f, T g⟫_ℝ
```

### Properties.lean

Replace `SchwartzMap D F` with `E` and `Configuration D F` with
`Configuration E` in all theorem signatures. Proofs unchanged.

### Dependency chain after refactor

```
NuclearSpace  →  Axioms (Schwartz instance)
     ↓
SpectralTheorem  →  NuclearSVD  →  NuclearFactorization
                                        ↓
                                  TargetFactorization
                                        ↓
                                  SeriesConvergence
                                        ↓
                                    Construction
                                        ↓
                                    Properties
```

## Target instances

### Phase 1: Schwartz space (refactor only)

```lean
instance : NuclearSpace (SchwartzMap D F)
```

Uses existing axioms. No new mathematics. Validates that the abstraction
works by recovering the current construction as a special case.

### Phase 2: C^∞(S^1) via Fourier basis

```lean
instance : NuclearSpace (PeriodicSchwartzMap ℝ)
```

Bypass Frechet manifold machinery entirely by working with periodic
smooth functions on ℝ, leveraging Mathlib's existing Fourier theory.

- **Basis:** Fourier modes e^{inx}, indexed by ℤ (biject to ℕ)
- **Seminorms:** Sobolev norms ‖f‖_k = ∑_n (1+|n|)^{2k} |f̂(n)|^2
- **Growth:** ‖e^{inx}‖_k = (1+|n|)^k — polynomial
- **Decay:** |f̂(n)| * (1+|n|)^k ≤ C * ‖f‖_{k+1} — super-polynomial

This is the simplest compact manifold case. The eigenbasis of d²/dx²
is explicit and the estimates are elementary.

Note: Mathlib does not yet have periodic smooth functions as a Frechet
space with `WithSeminorms`. This instance will require axioms analogous
to the current Schwartz axioms.

### Phase 3: C^∞(M) for compact Riemannian M

```lean
instance [CompactSpace M] [SmoothManifold M] [RiemannianMetric M] :
    NuclearSpace (SmoothMap M F)
```

- **Basis:** eigenfunctions of the Laplace-Beltrami operator
- **Growth:** Weyl asymptotics give eigenvalue growth ~ n^{2/dim M}
- **Decay:** smoothness gives super-polynomial decay of coefficients

More axioms needed; Weyl asymptotics for eigenvalue counting are not in
Mathlib. The proof structure is identical to S^1 with Weyl estimates
replacing explicit Fourier analysis.

### Phase 4: Lattice function spaces

```lean
instance [Fintype Λ] : NuclearSpace (Λ → ℝ)
```

Finite-dimensional spaces are trivially nuclear. The basis is the
standard basis {e_λ}, growth and decay are trivial since only
finitely many terms are nonzero.

For infinite lattices ℤ^d, work with rapidly decaying sequences:

```lean
instance : NuclearSpace (schwartzSeq (Fin d → ℤ))
```

where `schwartzSeq` denotes rapidly decaying sequences. Basis is the
standard basis; decay comes from the rapidly-decaying weights.

### Phase 5: Half-spaces via Laguerre basis

```lean
instance : NuclearSpace (SchwartzHalfLine)
```

Use Laguerre functions as the basis on ℝ₊. These are to the half-line
what Hermite functions are to ℝ. Growth and decay estimates are classical
and map 1:1 to the existing Hermite proofs.

The alternative (Seeley extension theorems to pull back from Schwartz
space on ℝ) requires formalizing extension operators that respect all
Frechet seminorms — much more difficult than direct Laguerre estimates.

### Phase 6: Tensor products via Kothe sequences

Given NuclearSpace instances for E and F, construct one for E ⊗ F.

**Key insight:** because `NuclearSpace` is defined via Schauder bases
(the Dynin-Mityagin / Kothe sequence space approach), we bypass the
abstract completed projective tensor product `⊗̂` entirely. Define:

```lean
def NuclearTensorProduct (E F : Type*) [NuclearSpace E] [NuclearSpace F] :=
  -- Kothe sequence space on ℕ × ℕ with product weights
  -- Frechet topology pulled back from the sequences
```

- **Basis:** ψ_i ⊗ φ_j via ℕ ≃ ℕ × ℕ (Cantor pairing)
- **Seminorms:** product weights w_{i,j}^{(k,l)} = p_k(ψ_i) * q_l(φ_j)
- **Growth:** product of individual growths (still polynomial)
- **Decay:** product of individual decays (still super-polynomial)

This gives the completed projective tensor product "for free" at the
sequence level, sidestepping abstract topological bornologies. Spaces
like S(ℝ^n) ⊗ C^∞(S^1) compose automatically.

## Technical risks

1. **Weighted embedding continuity.** The weighted ell2 embedding
   `nuclearEll2Embedding k` must be continuous from the Frechet topology.
   The proof uses: `coeff_decay` at level k gives a seminorm bound
   `‖j_k(f)‖_{ell2} ≤ C * p_q(f)`, and `WithSeminorms` implies continuity
   from a seminorm bound. This should be straightforward but is the main
   new proof in Phase 1.

2. **Mathlib gaps for compact manifolds.** `SmoothMap M F` is not yet a
   Frechet space in Mathlib. Eigenfunction theory for the Laplacian is
   absent. These instances will be axiom-backed for the foreseeable future.

3. **Universe polymorphism.** The bundled `ι : Type*` lives inside the
   class. Different instances use different index types (ℕ × ℕ for
   Schwartz, ℕ for Sobolev, Unit for finite-dimensional). Need to ensure
   universe levels don't cause issues in downstream theorems that are
   polymorphic over E.

4. **WeakDual for non-normed spaces.** Mathlib's `WeakDual` is defined
   for normed spaces. For a general locally convex E, the dual with
   weak-* topology may need a custom definition or use of
   `ContinuousLinearMap` with an explicit topology. Verify Mathlib
   compatibility before starting Construction.lean refactor.

## Implementation order

| Phase | Deliverable | New math? | Blocked by |
|---|---|---|---|
| 1 | NuclearSpace typeclass + Schwartz instance + refactor | No | Nothing |
| 2 | C^∞(S^1) via periodic functions + Fourier | Axioms for Fourier | Phase 1 |
| 3 | C^∞(M) via Laplacian eigenbasis | Axioms for Weyl | Phase 1 |
| 4 | Lattice spaces | Trivial | Phase 1 |
| 5 | Half-spaces via Laguerre | Axioms for Laguerre | Phase 1 |
| 6 | Tensor products via Kothe sequences | Kothe tensor definition | Phase 1 |

Phase 1 is the critical path. All other phases are independent of each
other and can proceed in parallel after Phase 1.

## Phase 1 checklist (COMPLETE)

- [x] Define `NuclearSpace` class in `NuclearSpace.lean`
- [x] Define weighted ℓ² embedding (inlined in `TargetFactorization.lean`)
- [x] Adjust 5 axiom signatures in `Axioms.lean` to match class fields
- [x] Package axioms as `schwartz_nuclearSpace` instance
- [x] Generalize `NuclearFactorization.lean`: SchwartzMap → E
- [x] Generalize `TargetFactorization.lean`: use weighted embedding
- [x] Verify `WeakDual` works for locally convex E (it does)
- [x] Generalize `Construction.lean`: Configuration E
- [x] Generalize `Properties.lean`: swap type signatures
- [x] Confirm `lake build` succeeds with no new sorry
