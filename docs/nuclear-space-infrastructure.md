# Nuclear Space Infrastructure

This directory contains ~1265 lines of Lean 4 defining the standard Pietsch
`NuclearSpace` typeclass, the stronger `DyninMityaginSpace` typeclass
(nuclearity via Schauder bases), the bridge theorem `DyninMityaginSpace.toNuclearSpace`,
and the canonical model `RapidDecaySeq` (the Köthe sequence space $s(\mathbb{N})$)
with its nuclear tensor product structure. This serves as the shared foundation
for both the Schwartz nuclearity proof (`SchwartzNuclear/`) and the Gaussian
field construction (`GaussianField/`).

**Status: Complete (0 sorrys, 0 axioms).**

## What Is a Nuclear Space?

### Pietsch nuclearity (standard definition)

A locally convex space $E$ is **nuclear** (in the sense of Pietsch) if for
every continuous seminorm $p$ there exists a dominating continuous seminorm
$q \ge p$, continuous linear functionals $f_n : E \to \mathbb{R}$, and
non-negative scalars $c_n$ with $\sum c_n < \infty$, such that:

1. $p(x) \le \sum_n |f_n(x)|\,c_n$ for all $x \in E$
2. $|f_n(x)| \le q(x)$ for all $x, n$

Equivalently, the canonical map $E_q \to E_p$ between seminorm completions
is a nuclear operator (trace-class). This is the standard definition used
in functional analysis (Pietsch, Grothendieck).

In Lean this is the typeclass [`NuclearSpace E`](../Nuclear/NuclearSpace.lean).

### Dynin-Mityagin characterization (basis form)

A stronger characterization applies to nuclear Fréchet spaces with a
Schauder basis. A locally convex space $E$ satisfies the
**Dynin-Mityagin condition** if it admits a Schauder basis $\{\psi_m\}$
whose expansion coefficients decay faster than any polynomial while
the basis vectors grow at most polynomially in every seminorm:

1. **Expansion**: every continuous linear functional $\varphi$ satisfies
   $\varphi(f) = \sum_m c_m(f)\,\varphi(\psi_m)$
2. **Basis growth**: $p_i(\psi_m) \le C\,(1+m)^s$ for each seminorm $p_i$
3. **Coefficient decay**: $|c_m(f)|\,(1+m)^k \le C\,p_S(f)$ for each $k$

The gap between polynomial growth and super-polynomial decay implies
Pietsch nuclearity (proved in [`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean)
as `DyninMityaginSpace.toNuclearSpace`). The converse holds for nuclear
Fréchet spaces that already possess a Schauder basis (the Dynin-Mityagin
theorem), but we do not formalize that direction.

In Lean this is the typeclass [`DyninMityaginSpace E`](../Nuclear/DyninMityagin.lean).
Our applications (Schwartz spaces) obtain the DM structure directly from the
Hermite basis.

## Why We Need It

The Gaussian field construction in `GaussianField/Construction.lean` requires a
nuclear factorization $T(f) = \sum_m c_m(f)\,y_m$ with $\sum \|y_m\| < \infty$.
This absolute convergence is what allows the Gaussian series
$\omega(f) = \sum_n \xi_n \langle e_n, T(f)\rangle$ (with iid $\xi_n \sim N(0,1)$)
to converge almost surely. Without nuclearity, the series need not converge and no
Gaussian measure exists in general.

The dependency flow is:

```
Nuclear/              (typeclasses + sequence space model)
    ^
    |
SchwartzNuclear/      (proves Schwartz space is nuclear)
    ^
    |
GaussianField/        (constructs Gaussian measures on nuclear spaces)
```

## File Structure

| File | Lines | Description |
|------|------:|-------------|
| [`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean) | 358 | `NuclearSpace` typeclass (Pietsch), Hahn-Banach for seminorms, DM→Pietsch bridge |
| [`DyninMityagin.lean`](../Nuclear/DyninMityagin.lean) | 76 | `DyninMityaginSpace` typeclass (DM characterization), Hilbert-space expansion theorem |
| [`NuclearTensorProduct.lean`](../Nuclear/NuclearTensorProduct.lean) | 831 | `RapidDecaySeq`, seminorms, `NuclearTensorProduct`, `pure` tensor embedding |
| **Total** | **~1265** | |

## What Is Proved

### NuclearSpace Typeclass ([`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean))

[`NuclearSpace E`](../Nuclear/NuclearSpace.lean#L57) is a `Prop`-valued typeclass
encoding Pietsch's characterization: for every continuous seminorm `p`, there exist
a dominating `q`, CLFs `fₙ`, and summable coefficients `cₙ` such that
`p(x) ≤ ∑ₙ ‖fₙ(x)‖ · cₙ` with `‖fₙ(x)‖ ≤ q(x)`.

The file also proves:

- [`exists_CLF_le_seminorm`](../Nuclear/NuclearSpace.lean#L73) — Hahn-Banach for
  continuous seminorms: given `q` and `f`, there exists a CLF `φ` with `φ(f) = q(f)`
  and `|φ| ≤ q`.
- [`seminorm_le_nuclear_expansion`](../Nuclear/NuclearSpace.lean#L169) — for a
  continuous seminorm `q` and a DM basis, `q(f) ≤ ∑ₘ |cₘ(f)| · q(ψₘ)`.
- [`DyninMityaginSpace.toNuclearSpace`](../Nuclear/NuclearSpace.lean#L240) — the
  bridge theorem: DM implies Pietsch. The proof constructs CLFs
  `fₘ = (1+m)^{S+2} · cₘ` and coefficients
  `aₘ = C₁ · sup_p(ψₘ) / (1+m)^{S+2}` (summable via the $1/m^2$ series).

### DyninMityaginSpace Typeclass ([`DyninMityagin.lean`](../Nuclear/DyninMityagin.lean))

[`DyninMityaginSpace E`](../Nuclear/DyninMityagin.lean#L41) bundles the seminorm family,
basis, and coefficients inside the class so that typeclass synthesis infers
everything from `E` alone. The expansion axiom is stated for scalar functionals
$\varphi : E \to \mathbb{R}$; the Hilbert-space form is recovered as:

[`DyninMityaginSpace.expansion_H`](../Nuclear/DyninMityagin.lean#L67): for any CLM
$T : E \to H$ and $w \in H$,
$$\langle w, T(f)\rangle = \sum_m c_m(f)\,\langle w, T(\psi_m)\rangle$$

This follows immediately by applying `DyninMityaginSpace.expansion` to the scalar CLF
$f \mapsto \langle w, T(f)\rangle$.

### Rapid Decay Sequences ([`NuclearTensorProduct.lean`](../Nuclear/NuclearTensorProduct.lean))

[`RapidDecaySeq`](../Nuclear/NuclearTensorProduct.lean#L43) is the Kothe sequence
space $s(\mathbb{N})$: real sequences $(a_m)$ such that
$\sum_m |a_m|\,(1+m)^k < \infty$ for every $k \in \mathbb{N}$.

The file builds up:

1. **Algebraic structure** (lines 62-113) — `AddCommGroup` and `Module ℝ` instances,
   with summability preserved under addition, negation, and scalar multiplication.

2. **Seminorm family** (lines 117-138) —
   [`rapidDecaySeminorm k`](../Nuclear/NuclearTensorProduct.lean#L118) $: a \mapsto \sum_m |a_m|\,(1+m)^k$.
   Proved to satisfy the seminorm axioms (triangle inequality via term-by-term
   bounds, homogeneity via `tsum_mul_left`).

3. **Topology** (lines 142-153) — the locally convex topology induced by the
   seminorm family, with `WithSeminorms`, `IsTopologicalAddGroup`, and
   `ContinuousSMul` instances.

4. **Standard basis and coefficients** (lines 157-204) —
   [`basisVec m`](../Nuclear/NuclearTensorProduct.lean#L158) (the $m$-th standard
   basis vector) and [`coeffCLM m`](../Nuclear/NuclearTensorProduct.lean#L190)
   (coordinate projection, continuous since $|a_m| \le$ `rapidDecaySeminorm 0 a`).

5. **DyninMityaginSpace instance** (lines 207-291) — the main result:
   [`rapidDecay_dyninMityaginSpace`](../Nuclear/NuclearTensorProduct.lean#L277).

   The key proof is [`hasSum_basisVec`](../Nuclear/NuclearTensorProduct.lean#L223):
   the partial sums $\sum_{m \in s} a_m\,e_m$ converge to $a$ in the seminorm
   topology. For each seminorm $k$ and $\varepsilon > 0$, the error
   $\sum_{m \notin s} |a_m|\,(1+m)^k$ is the tail of the convergent series
   `a.rapid_decay k`, hence eventually less than $\varepsilon$.

   The three `DyninMityaginSpace` fields then follow:
   - **Expansion**: apply CLM $\varphi$ to the convergent series
   - **Basis growth**: `rapidDecaySeminorm k (basisVec m) = (1+m)^k`, so $C = 1$, $s = k$
   - **Coefficient decay**: $|a_m|\,(1+m)^k \le \sum_n |a_n|\,(1+n)^k =$ `rapidDecaySeminorm k a`

### Nuclear Tensor Product

[`NuclearTensorProduct E₁ E₂`](../Nuclear/NuclearTensorProduct.lean) is
defined as `RapidDecaySeq` — mathematically justified by the Dynin-Mityagin
theorem: if $E_1 \cong s(\mathbb{N})$ and $E_2 \cong s(\mathbb{N})$, then
$E_1 \hat\otimes E_2 \cong s(\mathbb{N}^2) \cong s(\mathbb{N})$ via the Cantor
pairing $\mathbb{N}^2 \to \mathbb{N}$.

The key results are:
- `pure : E₁ → E₂ → NuclearTensorProduct E₁ E₂` — jointly continuous bilinear embedding
- `lift B : NuclearTensorProduct E₁ E₂ →L[ℝ] G` — universal property (factors bilinear maps)
- `lift_pure : lift B (pure e₁ e₂) = B e₁ e₂` — the factoring identity
- `NuclearTensorProduct.assoc` — associativity CLE (in `SchwartzTensorProduct.lean`)

For Schwartz spaces, the tensor product realizes the kernel theorem:
- `schwartzPeelOff d : S(ℝ^{d+2}) ≃L S(ℝ^{d+1}) ⊗̂ S(ℝ)` — dimension peeling
- `schwartzTensorEquiv m n : S(ℝ^{m+1}) ⊗̂ S(ℝ^{n+1}) ≃L S(ℝ^{m+n+2})` — general isomorphism

For the full construction details (Cantor pairing bounds, `pure` seminorm estimates,
`lift` convergence, reindexing automorphisms, associativity permutation), see
[tensor-products.md](tensor-products.md).

## Key Mathlib Dependencies

- `Mathlib.Analysis.LocallyConvex.WithSeminorms` — seminorm families, locally convex topologies
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum`, `Summable`
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product for `DyninMityaginSpace.expansion_H`
