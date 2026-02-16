# Lattice-to-Continuum Limit

## Goal

Given a sequence of Gaussian measures on lattice function spaces with spacing
$2^{-n}$, state and prove convergence to a continuum Gaussian measure. This
is the standard construction in constructive QFT and lattice field theory.

## Setup

### Continuum side

- $E$ = smooth functions on the target manifold (e.g., $C^\infty(T^2)$),
  a nuclear Fréchet space with `[NuclearSpace E]`
- $T : E \to H$ = continuum covariance operator
  (e.g., $(-\Delta + m^2)^{-1/2}$)
- `measure T` on `Configuration E` = the target Gaussian measure $\mu$

### Lattice side (for each $n$)

- $\Lambda_n = (\mathbb{Z}/2^n\mathbb{Z})^2$ (lattice with spacing $2^{-n}$)
- $E_n = \Lambda_n \to \mathbb{R}$ (finite-dimensional, trivially nuclear)
- $T_n : E_n \to H_n$ = discretized operator (e.g., discrete Laplacian)
- `measure T_n` on `Configuration E_n` = lattice Gaussian $\mu_n$

### The bridge

Restriction maps $r_n : E \to E_n$ that sample a smooth function at lattice
points (with appropriate $2^{-n}$ scaling). These are CLMs from the continuum
test function space to the lattice test function space.

## Convergence via characteristic functionals

The measures $\mu_n$ and $\mu$ live on different spaces ($E_n'$ vs $E'$),
so we pull the lattice measures into $E'$ via the dual maps
$r_n^* : E_n' \hookrightarrow E'$, defined by $(r_n^* \omega)(f) = \omega(r_n f)$.

Set $\nu_n = (r_n^*)_* \mu_n$, a measure on `Configuration E`.

The characteristic functional identity does the heavy lifting. For $\nu_n$:

$$\int_{E'} e^{i\omega(f)}\, d\nu_n = \int_{E_n'} e^{i\omega(r_n f)}\, d\mu_n = e^{-\frac{1}{2}\|T_n(r_n f)\|^2}$$

For $\mu$:

$$\int_{E'} e^{i\omega(f)}\, d\mu = e^{-\frac{1}{2}\|T(f)\|^2}$$

By Lévy's continuity theorem for nuclear spaces (the Bochner-Minlos theorem),
pointwise convergence of characteristic functionals on $E$ implies weak
convergence of measures on $E'$.

**The entire convergence problem reduces to:**

$$\|T_n(r_n f)\|_{H_n}^2 \to \|T(f)\|_H^2 \qquad \forall f \in E$$

That is: convergence of the discretized quadratic form to the continuum
quadratic form.

## Lean sketch

```lean
-- Lattice type for spacing 2^{-n}
abbrev Lattice (n : ℕ) := Fin (2^n) × Fin (2^n)

-- Lattice function space (trivially nuclear)
instance : NuclearSpace (Lattice n → ℝ) := ...  -- finite-dim

-- Restriction: sample smooth function at lattice points
variable (r : ∀ n, E →L[ℝ] (Lattice n → ℝ))

-- Lattice operators
variable (T_n : ∀ n, (Lattice n → ℝ) →L[ℝ] H_n)

-- Continuum operator
variable (T : E →L[ℝ] H)

-- THE KEY HYPOTHESIS: quadratic forms converge
variable (h_conv : ∀ f : E,
  Filter.Tendsto (fun n => ‖T_n n (r n f)‖ ^ 2) Filter.atTop
    (nhds (‖T f‖ ^ 2)))

-- Dual map: precomposition by r_n
def dualRestriction (n : ℕ) : Configuration (Lattice n → ℝ) → Configuration E :=
  fun ω => ω.comp (r n)

-- Pushed-forward lattice measures on Configuration E
def ν (n : ℕ) : Measure (Configuration E) :=
  (measure (T_n n)).map (dualRestriction r n)

-- GOAL: characteristic functionals converge pointwise
theorem lattice_continuum_charFun (f : E) :
    Filter.Tendsto
      (fun n => ∫ ω, Complex.exp (I * ↑(ω f)) ∂(ν r T_n n))
      Filter.atTop
      (nhds (∫ ω, Complex.exp (I * ↑(ω f)) ∂(measure T))) := by
  -- Both sides equal exp(-½ ‖...‖²) by charFun identity
  -- h_conv + continuity of exp gives the result
  sorry

-- Lévy continuity (Bochner-Minlos): charFun convergence ⟹ weak convergence
-- This is a substantial theorem, not yet in the library
```

## What the library provides

The characteristic functional identity `charFun T f` is the key tool.
It converts the measure-theoretic convergence question into a purely
analytic question about operator norms: does $\|T_n(r_n f)\|^2 \to \|T(f)\|^2$?

The library handles:
- Construction of each `measure T_n` and `measure T`
- The `IsProbabilityMeasure` instances
- The characteristic functional identities on both sides
- Moment identities (centered, second moment = covariance)

## What's needed beyond the current library

1. **Finite-dimensional `NuclearSpace` instance.** For $\Lambda_n \to \mathbb{R}$
   this is trivial: standard basis, identity coefficients, all sums finite.

2. **Dual maps and pushforward.** Given $r_n : E \to E_n$, the dual map
   $r_n^* : E_n' \to E'$ defined by $(r_n^* \omega)(f) = \omega(r_n f)$,
   and the pushforward $(r_n^*)_* \mu_n$. This is straightforward —
   $r_n^*$ is just precomposition.

3. **Lévy continuity for nuclear spaces.** Pointwise convergence of
   characteristic functionals on $E$ implies weak convergence on $E'$.
   This is the Bochner-Minlos theorem (converse direction). It is a
   substantial result not currently in Mathlib.

4. **Quadratic form convergence.** The hypothesis
   $\|T_n(r_n f)\|^2 \to \|T(f)\|^2$ is problem-specific. For the
   Gaussian free field, this amounts to proving that the discrete
   Laplacian approximates the continuum Laplacian in the appropriate
   sense. This is where the actual analysis lives.
