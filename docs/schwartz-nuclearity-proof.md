# Schwartz Space Nuclearity — Proof

This directory contains ~7,700 lines of Lean 4 proving that
Schwartz space $\mathcal{S}(\mathbb{R}^d, \mathbb{R})$ is a nuclear Fréchet space,
i.e., constructing a `NuclearSpace (SchwartzMap D ℝ)` instance from first principles.

**Status: Complete (0 sorrys, 0 axioms).**

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

| File | Lines | Description |
|------|------:|-------------|
| [`HermiteFunctions.lean`](../SchwartzNuclear/HermiteFunctions.lean) | 1,853 | 1D Hermite functions, orthonormality, completeness |
| [`SchwartzHermiteExpansion.lean`](../SchwartzNuclear/SchwartzHermiteExpansion.lean) | 1,446 | 1D Schwartz-Hermite expansion, coefficient decay |
| [`Basis1D.lean`](../SchwartzNuclear/Basis1D.lean) | 157 | 1D NuclearSpace fields assembly |
| [`ParametricCalculus.lean`](../SchwartzNuclear/ParametricCalculus.lean) | 316 | Differentiation under the integral sign |
| [`SchwartzSlicing.lean`](../SchwartzNuclear/SchwartzSlicing.lean) | 1,134 | Multi-d slicing and partial Hermite coefficients |
| [`HermiteTensorProduct.lean`](../SchwartzNuclear/HermiteTensorProduct.lean) | 2,619 | Multi-d isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq` |
| [`HermiteNuclear.lean`](../SchwartzNuclear/HermiteNuclear.lean) | 174 | `NuclearSpace` instance from the isomorphism |
| **Total** | **7,699** | |

## What Is Proved

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

### Parametric Calculus (`ParametricCalculus.lean`)

- **`norm_iteratedFDeriv_iteratedFDeriv`** — iterated Fréchet derivative of the
  map $y \mapsto D^m f(y, t)$ decomposes as $D^l_y D^m_{(y,t)} f$, bounded by
  $D^{l+m} f$.

- **`contDiff_schwartz_parametric_integral`** — if $f : Y \to \mathcal{S}(T, F)$
  is $C^n$ in $y$ and the map $y \mapsto f(y)$ is Schwartz-valued, then
  $y \mapsto \int f(y)(t)\,g(t)\,dt$ is $C^n$.

### Multi-d Slicing (`SchwartzSlicing.lean`)

- **`schwartz_slice_y`** — for $f \in \mathcal{S}(\mathbb{R}^{d+2})$, the
  slice $t \mapsto f(y, t)$ is Schwartz in $t$, proved via
  `SchwartzMap.compCLMOfAntilipschitz` (the embedding $t \mapsto (y,t)$ is
  isometric and has temperate growth).

- **`schwartz_partial_hermiteCoeff`** — the partial Hermite coefficient
  $g_n(y) = \int f(y, t)\,\psi_n(t)\,dt$ is Schwartz in $y$, with full
  smoothness and decay proved via parametric calculus and CLM chain rules.

- **`schwartz_partial_hermiteCoeff_seminorm_bound`** — the weighted seminorm
  bound $p_{k',l'}(g_n) \cdot (1+n)^k \le C \cdot \sup_{q'} p_{q'}(f)$,
  proved by scalarization: evaluate $D^{l'}_y[g_n]$ along arbitrary vectors $v$,
  reducing to a 1D problem solvable by `hermiteCoeff1D_decay`.

### 1D Sequence Space Isomorphism (`HermiteTensorProduct.lean`, lines 110-600)

- **`schwartzRapidDecayEquiv1D`** — the topological isomorphism
  $\mathcal{S}(\mathbb{R}) \cong s(\mathbb{N})$, constructed as a
  `ContinuousLinearEquiv` with:
  - Forward: $f \mapsto (c_n(f))_n$ (proved to be a CLM, coefficients are rapid-decay)
  - Backward: $(a_n)_n \mapsto \sum_n a_n\,\psi_n$ (proved to converge in Schwartz topology,
    with CLM seminorm bounds)
  - Left inverse: forward $\circ$ backward = id (by Kronecker property)
  - Right inverse: backward $\circ$ forward = id (by Hermite completeness/injectivity)

### Multi-Dimensional Structure (`HermiteTensorProduct.lean`, lines 600-1100)

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

### Multi-d Coefficient Decay — The Slicing Trick

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
    unweighted bound
  - $k \ge 0$: factor $(1+|\alpha|)^k \le (1+|\alpha_{\mathrm{rest}}|)^k \cdot (1+n)^k$,
    apply IH for the first factor and weighted seminorm bound for the second

### Multi-d Backward Map and Final Assembly (`HermiteTensorProduct.lean` lines 2026-2619, `HermiteNuclear.lean`)

The backward map $(a_n)_n \mapsto \sum_n a_n\,\Phi_n$ (where $\Phi_n$ is the
flattened multi-d basis) is fully proved:
- Schwartz convergence of the expansion
- CLM property with seminorm bounds
- Kronecker property for the right inverse

The [`NuclearSpace` instance](../SchwartzNuclear/HermiteNuclear.lean#L156) is assembled in `HermiteNuclear.lean`:
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

## Dependency Graph

```
HermiteFunctions                         [1D Hermite functions]
    |
SchwartzHermiteExpansion                 [1D expansion + decay]
    |
Basis1D                                  [1D NuclearSpace fields]
    |
ParametricCalculus ──────────────┐
    |                            |
SchwartzSlicing                  |       [multi-d slicing + scalarization]
    |                            |
HermiteTensorProduct ────────────┘       [multi-d isomorphism ≃L RapidDecaySeq]
    |
HermiteNuclear                           [NuclearSpace instance]
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
