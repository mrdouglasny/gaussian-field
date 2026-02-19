# Schwartz Space Nuclearity — Proof Attempts

This directory contains ~6,300 lines of Lean 4 toward proving that
Schwartz space $\mathcal{S}(\mathbb{R}^d, \mathbb{R})$ is a nuclear Fréchet space,
i.e., constructing a `NuclearSpace (SchwartzMap D ℝ)` instance from first principles.

The main library (`GaussianField/Axioms.lean`) currently states nuclearity as
a single axiom. This directory is WIP toward eliminating that axiom.

## Overall Strategy

The proof follows the classical Dynin-Mityagin approach:

$$\mathcal{S}(\mathbb{R}^d) \cong s(\mathbb{N})$$

where $s(\mathbb{N})$ is the space of rapidly decreasing sequences, and the
isomorphism is the Hermite expansion $f \mapsto (c_n(f))_n$ with
$c_n(f) = \int f(x)\,\psi_n(x)\,dx$ and $\psi_n$ the Hermite functions.

The `NuclearSpace` instance is then transferred through this continuous linear
equivalence, using:
- **Expansion**: $\varphi(f) = \sum_n c_n(f)\,\varphi(\psi_n)$ for all CLFs $\varphi$
- **Basis growth**: $p_{k,l}(\psi_n) \le C\,(1+n)^s$ (polynomial in $n$)
- **Coefficient decay**: $|c_n(f)|\,(1+n)^k \le C\,p_q(f)$ (super-polynomial)

## File Structure

| File | Lines | Sorrys | Axioms | Status |
|------|------:|:------:|:------:|--------|
| `HermiteFunctions.lean` | 1,853 | 0 | 0 | **Complete** |
| `SchwartzHermiteExpansion.lean` | 1,446 | 0 | 0 | **Complete** |
| `Basis1D.lean` | 157 | 0 | 0 | **Complete** |
| `SchwartzSlicing.lean` | 195 | 5 | 0 | Partial |
| `HermiteTensorProduct.lean` | 2,760 | 0 | 0 | Partial |
| **Total** | **6,440** | **5** | **0** | |

## What Is Proved (no axioms, no sorrys)

### 1D Hermite Function Theory (`HermiteFunctions.lean`)

All 1D infrastructure is fully proved from Mathlib primitives:

- **`hermiteFunction n x`** — the $n$-th Hermite function
  $\psi_n(x) = c_n\,H_n(x\sqrt{2})\,e^{-x^2/2}$ where $H_n$ is the
  probabilist's Hermite polynomial (from `Mathlib.RingTheory.Polynomial.Hermite`)

- **`hermiteFunction_orthonormal`** — $\int \psi_n\,\psi_m = \delta_{nm}$.
  Proved via integration by parts, computing the "J-integral"
  $J(n,m) = \int H_n(x\sqrt{2})\,H_m(x\sqrt{2})\,e^{-x^2}\,dx$ by induction.

- **`hermiteFunction_schwartz`** — $\psi_n \in \mathcal{S}(\mathbb{R})$.
  Proved by showing Hermite functions are iterated derivatives of the
  Gaussian $e^{-x^2/2}$ (which is Schwartz), using Mathlib's `derivCLM`.

- **`mul_x_hermiteFunction`** / **`deriv_hermiteFunction`** — the raising/lowering
  relations:
  $$x\,\psi_n = \tfrac{\sqrt{n+1}}{\sqrt{2}}\,\psi_{n+1} + \tfrac{\sqrt{n}}{\sqrt{2}}\,\psi_{n-1}$$
  $$\psi_n' = \tfrac{\sqrt{n}}{\sqrt{2}}\,\psi_{n-1} - \tfrac{\sqrt{n+1}}{\sqrt{2}}\,\psi_{n+1}$$

- **`hermiteFunction_seminorm_bound`** — $p_{k,l}(\psi_n) \le C\,(1+n)^s$
  for some $C, s$ depending on $k, l$. Proved by iterating the raising/lowering
  operators to express $x^k\,\psi_n^{(l)}$ as a finite sum of $\psi_j$ with
  polynomially-bounded coefficients, then using the $L^\infty$ bound
  $\|\psi_n\|_\infty \le 1$ (from the energy identity $\|\psi_n'\|_2^2 + \|x\psi_n\|_2^2 = 2n+1$).

- **`hermiteFunction_complete`** — if $\int f\,\psi_n = 0$ for all $n$, then
  $f = 0$ a.e. The proof:
  1. Orthogonality to all $\psi_n$ implies all moments $\int f(x)\,x^k\,e^{-x^2}\,dx = 0$
     (since $\psi_n$ spans all polynomial-times-Gaussian functions up to degree $n$)
  2. Therefore $\int f(x)\,P(x)\,e^{-x^2}\,dx = 0$ for all polynomials $P$
  3. The Fourier transform of $g(x) = f(x)\,e^{-x^2/2}$ vanishes
     (moment vanishing implies $\hat{g}$ has vanishing Taylor series, plus
     Fourier inversion via `Mathlib.Analysis.Fourier.Inversion`)
  4. By Fourier injectivity, $g = 0$ a.e., hence $f = 0$ a.e.

### 1D Schwartz-Hermite Expansion (`SchwartzHermiteExpansion.lean`)

- **`hermiteCoeff1D n f`** — $c_n(f) = \int f(x)\,\psi_n(x)\,dx$

- **`hermiteFunction_harmonic_oscillator_eigenvalue`** —
  $(-\partial^2 + x^2)\psi_n = (2n+1)\psi_n$ (pointwise identity, proved from
  raising/lowering operators)

- **`hermiteCoeff_harmonic_oscillator`** —
  $c_n(Hf) = (2n+1)\,c_n(f)$ where $H = -\partial^2 + x^2$ is the harmonic
  oscillator. Proved via `schwartz_integration_by_parts_twice`.

- **`harmonicOscillator`** — the harmonic oscillator $H = -\partial^2 + x^2$
  as a continuous linear map `SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ`, constructed
  from Mathlib's `SchwartzMap.derivCLM` and multiplication CLM.

- **`hermiteCoeff1D_decay`** — super-polynomial decay:
  $$|c_n(f)|\,(1+n)^k \le C\,p_q(f) \qquad \forall k \in \mathbb{R}$$
  The proof: choose $m = \lceil k \rceil$, then
  $|c_n(f)|\,(2n+1)^m = |c_n(H^m f)| \le \|H^m f\|_{L^2} \le C\,p_q(H^m f)
  \le C'\,p_{q'}(f)$ by Cauchy-Schwarz and CLM continuity of $H^m$.

- **`schwartz_hermite_hasSum`** —
  $f = \sum_n c_n(f)\,\psi_n$ converges in the Schwartz topology.
  The limit is identified with $f$ by: (a) showing the partial sums converge
  in $L^2$ (Bessel/Parseval), (b) the Schwartz limit agrees with the $L^2$
  limit pointwise (by dominated convergence + seminorm summability), (c) using
  `hermiteFunction_complete` to conclude.

- **`schwartz_hermite_expansion_1D`** — for any CLM $T : \mathcal{S} \to H$,
  $T(f) = \sum_n c_n(f)\,T(\psi_n)$ (follows from continuity of $T$ applied
  to the Schwartz-topology convergence).

### 1D Nuclear Schauder Basis Assembly (`Basis1D.lean`)

Packages the above into the three `NuclearSpace` fields:
- **`schwartz_hermite_expansion_CLF`** — expansion for scalar CLFs
- **`schwartzHermiteBasis1D_growth`** — polynomial growth bound
- **`hermiteCoeff1D_decay_single`** — decay with $\mathbb{N}$ exponent

Also constructs **`hermiteCoeff1DCLM`** — the Hermite coefficient as a
continuous linear map, with continuity proved from the decay bound at $k = 0$.

### 1D Sequence Space Isomorphism (`HermiteTensorProduct.lean`, lines 110–600)

- **`schwartzRapidDecayEquiv1D`** — the topological isomorphism
  $\mathcal{S}(\mathbb{R}) \cong s(\mathbb{N})$, constructed as a
  `ContinuousLinearEquiv` with:
  - Forward: $f \mapsto (c_n(f))_n$ (proved to be a CLM, coefficients are rapid-decay)
  - Backward: $(a_n)_n \mapsto \sum_n a_n\,\psi_n$ (proved to converge in Schwartz topology,
    with CLM seminorm bounds)
  - Left inverse: forward ∘ backward = id (by Kronecker property)
  - Right inverse: backward ∘ forward = id (by Hermite completeness/injectivity)

### Multi-Dimensional Structure (`HermiteTensorProduct.lean`, lines 600–1100)

- **Multi-index flattening** — bijection $\mathbb{N}^d \to \mathbb{N}$ via iterated
  Cantor pairing, with proved polynomial growth bounds in both directions
  (`multiIndexEquiv_growth`, `multiIndexEquiv_symm_growth`)

- **`hermiteFunctionNd d α x`** — the tensor-product Hermite function
  $\Psi_\alpha(x) = \prod_i \psi_{\alpha_i}(x_i)$

- **`schwartzHermiteBasisNd d α`** — $\Psi_\alpha$ as a Schwartz map, with proved
  smoothness, Schwartz decay, and polynomial seminorm growth

- **`hermiteCoeffNd d α f`** — multi-d Hermite coefficient
  $c_\alpha(f) = \int f(x)\,\Psi_\alpha(x)\,dx$

- **`hermiteFunctionNd_orthonormal`** — $\int \Psi_\alpha\,\Psi_\beta = \delta_{\alpha\beta}$
  (from 1D orthonormality + Fubini)

### Multi-D Backward Map and Final Assembly (lines 2026–2643)

The backward map $(a_n)_n \mapsto \sum_n a_n\,\Phi_n$ (where $\Phi_n$ is the
flattened multi-d basis) is fully proved:
- Schwartz convergence of the expansion
- CLM property with seminorm bounds
- Kronecker property for the right inverse

The `NuclearSpace` instance is assembled at the end:
```lean
noncomputable instance schwartz_nuclearSpace [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D ℝ
  basis m := (schwartzRapidDecayEquiv D).symm (RapidDecaySeq.basisVec m)
  coeff m := (RapidDecaySeq.coeffCLM m).comp (schwartzRapidDecayEquiv D).toContinuousLinearMap
  expansion := schwartz_expansion_from_equiv (schwartzRapidDecayEquiv D)
  basis_growth := schwartz_basis_growth_from_equiv (schwartzRapidDecayEquiv D)
  coeff_decay := schwartz_coeff_decay_from_equiv (schwartzRapidDecayEquiv D)
```

## Remaining Gaps (5 sorrys, 0 axioms)

### Sorrys in `SchwartzSlicing.lean`

**`contDiff_parametric_hermiteCoeff`** — smoothness and iterated derivative
commutation for $y \mapsto \int f(y, t)\,\psi_n(t)\,dt$.
Requires iterated differentiation under the integral sign, not yet available
in Mathlib (only single-step `hasFDerivAt_integral_of_dominated_of_fderiv_le`).

**`schwartz_slice_partial.smooth'` / `decay'`** — smoothness and Schwartz decay
of the scalarized slice $t \mapsto D^{l'}_y[f(\cdot, t)](y)(v)$.
Follows from joint smoothness and decay of $f$.

**`schwartz_partial_hermiteCoeff_iteratedFDeriv`** — the iterated derivative of
$g_n(y) = \int f(y, t)\,\psi_n(t)\,dt$ evaluated at $y$ along vectors $v$ equals
the 1D Hermite coefficient of the corresponding scalarized slice.

**`schwartz_slice_partial_seminorm_bound`** — 1D Schwartz seminorm of the
scalarized slice, weighted by $\|y\|^{k'}$, is bounded by
$C \cdot \prod\|v_i\| \cdot \sup_{q'} p_{q'}(f)$.

### Former Axiom (now proved)

**`schwartz_partial_hermiteCoeff_seminorm_bound`** (`HermiteTensorProduct.lean`)
— previously an axiom, now proved by "scalarization": evaluate the multilinear
map $D^{l'}_y[g_n]$ along arbitrary vectors $v$, reducing to a 1D problem
solvable by `hermiteCoeff1D_decay`.

### Golden Slicing Trick

The multi-dimensional coefficient decay (`hermiteCoeffNd_decay`) is proved by
**induction on dimension**, using the Fubini factorization
$c_\alpha(f) = c_{\alpha_{\mathrm{rest}}}(g_{\alpha_{\mathrm{last}}})$
where $g_n = \mathrm{schwartz\_partial\_hermiteCoeff}\;d\;f\;n$.

- **Base case** ($d = 1$): transfers through the CLE `euclideanFin1Equiv` to
  the proved 1D decay theorem, using `Seminorm.bound_of_continuous` for the
  seminorm transfer.

- **Inductive step**: case split on the exponent $k$:
  - $k < 0$: $(1+|\alpha|)^k \le (1+|\alpha_{\mathrm{rest}}|)^k$ directly
    (since $|\alpha| \ge |\alpha_{\mathrm{rest}}|$ and $k < 0$), then IH +
    unweighted axiom
  - $k \ge 0$: factor $(1+|\alpha|)^k \le (1+|\alpha_{\mathrm{rest}}|)^k \cdot (1+n)^k$,
    apply IH for the first factor and weighted seminorm bound for the second

This approach replaced the original 3 axioms (B1: L2 bound, B2: coordinate
harmonic oscillator CLM, B3: eigenvalue identity) with a single seminorm
control lemma (now proved via scalarization).

## What Was Resolved

### `schwartz_slice` (A1) — fully proved

The slicing construction $t \mapsto f(y, t)$ for fixed $y$ was originally 4 sorrys.
Both `smooth'` and `decay'` were proved using Mathlib's
`SchwartzMap.compCLMOfAntilipschitz`: if $g$ has temperate growth and is
antilipschitz, then $f \circ g \in \mathcal{S}$.

Key helper lemmas:
- **`euclideanSnoc_hasTemperateGrowth`** — the embedding $t \mapsto (y, t)$ has
  temperate growth, proved via `HasTemperateGrowth.of_pi` (decomposing into
  constant + linear components per coordinate)
- **`euclideanSnoc_antilipschitz`** — the embedding is isometric (hence antilipschitz
  with constant 1), proved by computing $\mathrm{dist}(g(s), g(t)) = |s - t|$

### `schwartz_partial_hermiteCoeff_decay` — proved

The Schwartz decay of $y \mapsto \int f(y,t)\,\psi_n(t)\,dt$ (assuming
derivative commutation from `contDiff_parametric_hermiteCoeff`) uses:

- **`schwartz_slice_y_le_seminorm`** — pointwise bound
  $\|y\|^k \cdot \|\partial^m_y(f \circ \mathrm{snoc}(\cdot, t))(y)\| \le p_{k,m}(f)$,
  proved via the chain rule for the affine isometric embedding
  $y \mapsto (y, t)$ using `ContinuousLinearMap.iteratedFDeriv_comp_right`,
  `iteratedFDeriv_comp_add_left`, and `euclideanSnoc_norm_ge_left`.
- **`integral_euclidean_snoc`** — Fubini for EuclideanSpace slicing, now fully proved.

### `integral_euclidean_snoc` — proved

The Fubini factorization $\int_{\mathbb{R}^{d+2}} g = \int_{\mathbb{R}^{d+1}} \int_{\mathbb{R}} g(y,t)\,dt\,dy$
proved using `MeasureTheory.integral_prod`, `PiLp.volume_preserving_toLp`,
and `MeasurableEquiv.piFinSuccAbove`.

## Dependency Graph

```
HermiteFunctions.lean                    [1D: complete]
    ↓
SchwartzHermiteExpansion.lean            [1D expansion: complete]
    ↓
Basis1D.lean                             [1D NuclearSpace fields: complete]
    ↓
SchwartzSlicing.lean                     [multi-d slicing: 5 sorrys]
    ↓
HermiteTensorProduct.lean                [multi-d isomorphism + instance: 0 axioms]
```

## Key Mathlib Dependencies

- `Mathlib.RingTheory.Polynomial.Hermite` — Hermite polynomials $H_n$
- `Mathlib.Analysis.SpecialFunctions.Gaussian` — Gaussian integrals
- `Mathlib.Analysis.Distribution.SchwartzSpace` — Schwartz maps, seminorms, `derivCLM`
- `Mathlib.Analysis.Distribution.TemperateGrowth` — `HasTemperateGrowth`, `compCLMOfAntilipschitz`
- `Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff` — Fourier uniqueness for completeness proof
- `Mathlib.Analysis.Fourier.Inversion` — Fourier inversion theorem
- `Mathlib.MeasureTheory.Integral.Pi` — product measure integrals
- `Mathlib.Topology.Algebra.InfiniteSum` — tsum in topological spaces
