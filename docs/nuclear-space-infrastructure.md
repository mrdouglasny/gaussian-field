# Nuclear Space Infrastructure

This directory contains ~430 lines of Lean 4 defining the `NuclearSpace` typeclass
and the canonical model `RapidDecaySeq` (the Kothe sequence space $s(\mathbb{N})$),
which serves as the shared foundation for both the Schwartz nuclearity proof
(`SchwartzNuclear/`) and the Gaussian field construction (`GaussianField/`).

**Status: Complete (0 sorrys, 0 axioms).**

## What Is a Nuclear Space?

A locally convex space $E$ is **nuclear** if it admits a Schauder basis
$\{\psi_m\}$ whose expansion coefficients decay faster than any polynomial
while the basis vectors grow at most polynomially in every seminorm. Precisely:

1. **Expansion**: every continuous linear functional $\varphi$ satisfies
   $\varphi(f) = \sum_m c_m(f)\,\varphi(\psi_m)$
2. **Basis growth**: $p_i(\psi_m) \le C\,(1+m)^s$ for each seminorm $p_i$
3. **Coefficient decay**: $|c_m(f)|\,(1+m)^k \le C\,p_S(f)$ for each $k$

This gap between polynomial growth and super-polynomial decay is the
**nuclear property**. It implies that every continuous linear map out of $E$
into a Hilbert space factors through an absolutely summable sequence of
rank-one operators — the key ingredient for constructing Gaussian measures.

## Why We Need It

The Gaussian field construction in `GaussianField/Construction.lean` requires a
nuclear factorization $T(f) = \sum_m c_m(f)\,y_m$ with $\sum \|y_m\| < \infty$.
This absolute convergence is what allows the Gaussian series
$\omega(f) = \sum_n \xi_n \langle e_n, T(f)\rangle$ (with iid $\xi_n \sim N(0,1)$)
to converge almost surely. Without nuclearity, the series need not converge and no
Gaussian measure exists in general.

The dependency flow is:

```
Nuclear/              (typeclass + sequence space model)
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
| [`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean) | 76 | `NuclearSpace` typeclass, Hilbert-space expansion theorem |
| [`NuclearTensorProduct.lean`](../Nuclear/NuclearTensorProduct.lean) | 355 | `RapidDecaySeq`, seminorms, `NuclearTensorProduct` |
| **Total** | **431** | |

## What Is Proved

### NuclearSpace Typeclass ([`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean))

[`NuclearSpace E`](../Nuclear/NuclearSpace.lean#L41) bundles the seminorm family,
basis, and coefficients inside the class so that typeclass synthesis infers
everything from `E` alone. The expansion axiom is stated for scalar functionals
$\varphi : E \to \mathbb{R}$; the Hilbert-space form is recovered as:

[`NuclearSpace.expansion_H`](../Nuclear/NuclearSpace.lean#L67): for any CLM
$T : E \to H$ and $w \in H$,
$$\langle w, T(f)\rangle = \sum_m c_m(f)\,\langle w, T(\psi_m)\rangle$$

This follows immediately by applying `expansion` to the scalar CLF
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

5. **NuclearSpace instance** (lines 207-291) — the main result:
   [`rapidDecay_nuclearSpace`](../Nuclear/NuclearTensorProduct.lean#L277).

   The key proof is [`hasSum_basisVec`](../Nuclear/NuclearTensorProduct.lean#L223):
   the partial sums $\sum_{m \in s} a_m\,e_m$ converge to $a$ in the seminorm
   topology. For each seminorm $k$ and $\varepsilon > 0$, the error
   $\sum_{m \notin s} |a_m|\,(1+m)^k$ is the tail of the convergent series
   `a.rapid_decay k`, hence eventually less than $\varepsilon$.

   The three `NuclearSpace` fields then follow:
   - **Expansion**: apply CLM $\varphi$ to the convergent series
   - **Basis growth**: `rapidDecaySeminorm k (basisVec m) = (1+m)^k`, so $C = 1$, $s = k$
   - **Coefficient decay**: $|a_m|\,(1+m)^k \le \sum_n |a_n|\,(1+n)^k =$ `rapidDecaySeminorm k a`

### Nuclear Tensor Product (lines 296-355)

[`NuclearTensorProduct E₁ E₂`](../Nuclear/NuclearTensorProduct.lean#L314) is
defined as `RapidDecaySeq` — mathematically justified by the Dynin-Mityagin
theorem: if $E_1 \cong s(\mathbb{N})$ and $E_2 \cong s(\mathbb{N})$, then
$E_1 \hat\otimes E_2 \cong s(\mathbb{N}^2) \cong s(\mathbb{N})$ via the Cantor
pairing $\mathbb{N}^2 \to \mathbb{N}$.

The file provides:
- [`fromPairIndex`](../Nuclear/NuclearTensorProduct.lean#L340) / [`toPairIndex`](../Nuclear/NuclearTensorProduct.lean#L343) — Cantor pairing wrappers
- [`nat_pair_bound`](../Nuclear/NuclearTensorProduct.lean#L298) — $\text{pair}(n,m) \le (n+m+1)^2$ (used for growth bounds in `SchwartzNuclear/`)
- Inherited `NuclearSpace` instance via `rapidDecay_nuclearSpace`

## Key Mathlib Dependencies

- `Mathlib.Analysis.LocallyConvex.WithSeminorms` — seminorm families, locally convex topologies
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum`, `Summable`
- `Mathlib.Analysis.InnerProductSpace.Basic` — inner product for `expansion_H`
