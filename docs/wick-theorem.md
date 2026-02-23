# Wick's Theorem (Isserlis' Theorem)

**File:** [`GaussianField/Wick.lean`](../GaussianField/Wick.lean) (1,067 lines, sorry-free)

Wick's theorem expresses the n-point functions of a centered Gaussian measure
in terms of the 2-point function (covariance). This is the combinatorial heart
of free-field QFT, and is also known as Isserlis' theorem in probability.

## Main results

### Gaussian integration by parts

**`gaussian_ibp`** — Base case. For a single evaluation functional times the
characteristic exponential:

$$\mathbb{E}[\omega(f_0) \cdot e^{i\omega(h)}] = i \langle Tf_0, Th\rangle \cdot \mathbb{E}[e^{i\omega(h)}]$$

**`gaussian_ibp_general`** — Full inductive version with polynomial weight.
For n+1 test functions g\_0, ..., g\_n and a "spectral parameter" h:

$$\mathbb{E}\left[\omega(f_0) \prod_{i=0}^n \omega(g_i) \cdot e^{i\omega(h)}\right] = \sum_{j=0}^n \langle Tf_0, Tg_j\rangle \cdot \mathbb{E}\left[\prod_{i \neq j} \omega(g_i) \cdot e^{i\omega(h)}\right] + i \langle Tf_0, Th\rangle \cdot \mathbb{E}\left[\prod_i \omega(g_i) \cdot e^{i\omega(h)}\right]$$

The `exp(i*omega(h))` factor is the Fourier-analytic handle that drives the induction:
differentiating with respect to a parameter t in `exp(i*omega(t*g + h))`
brings down `i*omega(g)` factors, relating the (n+1)-point integral to n-point integrals.

### Wick's recursive formula

**`wick_recursive`** — Setting h = 0 in `gaussian_ibp_general` kills the
exponential (exp(0) = 1) and the last term (inner(Tf\_0, T(0)) = 0),
giving the purely polynomial identity:

$$\mathbb{E}\left[\omega(f_0) \prod_{i=0}^n \omega(g_i)\right] = \sum_{j=0}^n \langle Tf_0, Tg_j\rangle \cdot \mathbb{E}\left[\prod_{i \neq j} \omega(g_i)\right]$$

This is Wick's theorem in recursive form: pick a partner g\_j for f\_0,
extract the covariance `inner(Tf_0, Tg_j)`, and recurse on the remaining variables.

### Odd moments vanish

**`odd_moment_vanish`** — For a centered Gaussian measure, all odd moments are zero:

$$\mathbb{E}\left[\prod_{i=0}^{2k} \omega(f_i)\right] = 0$$

Proof by induction on k: `wick_recursive` expresses the (2k+1)-point function
as a sum of (2k-1)-point functions, which vanish by the inductive hypothesis.

### Wick bound

**`wick_bound`** — Bound on n-point functions:

$$\left|\mathbb{E}\left[\prod_{i=0}^{n-1} \omega(f_i)\right]\right| \leq (n-1)!! \cdot \prod_i \|T(f_i)\|$$

Proof by induction using `wick_recursive` and Cauchy-Schwarz at each step.
The (n-1)!! factor counts the number of perfect pairings of n elements.

**`wick_bound_factorial`** — Factorial form suitable for OS1':

$$\left|\mathbb{E}\left[\prod_i \omega(f_i)\right]\right| \leq \sqrt{n!} \cdot \prod_i \|T(f_i)\|$$

Uses the auxiliary lemma `double_factorial_le_sqrt_factorial`: (n-1)!! &le; sqrt(n!).

## Lean API reference

| Definition / Theorem | Signature | Description |
|---|---|---|
| `product_integrable` | `Integrable (fun w => prod i, w (f i)) (measure T)` | Products of evaluation functionals are integrable |
| `gaussian_ibp` | integral identity | IBP for single evaluation x exponential |
| `gaussian_ibp_general` | integral identity | IBP for polynomial x exponential |
| `wick_recursive` | integral identity | Recursive Wick formula (h = 0 specialization) |
| `odd_moment_vanish` | `integral w, prod i, w (f i) d(measure T) = 0` | Odd moments vanish |
| `wick_bound` | norm bound | (n-1)!! bound on n-point functions |
| `wick_bound_factorial` | norm bound | sqrt(n!) bound on n-point functions |
| `double_factorial_le_sqrt_factorial` | `((n-1)!! : R) <= n!^(1/2)` | Auxiliary inequality |

## Proof architecture

The proof is organized in three layers:

### Layer 1: Differentiation under the integral

**`hasDerivAt_weighted_exp_leibniz`** — Leibniz rule for
d/dt at t=0 of `integral P(w) * exp(i*w(t*g + h)) d mu`.

The polynomial weight P(w) is constant in t, so the derivative at
t = 0 simply brings down `i*w(g)` from the exponential. Domination
is by `||P(w)|| * ||w(g)||`, integrable when P is a product
of evaluation functionals (via Holder escalation in `product_integrable`).

### Layer 2: Gaussian IBP by characteristic functional

The base `gaussian_ibp` follows from differentiating the characteristic
functional E[exp(i w(f))] = exp(-1/2 ||Tf||^2) in two ways:

1. **Closed form** (`hasDerivAt_charFun_closed`): differentiate the Gaussian
   exp(-1/2 ||T(t f\_0 + h)||^2) directly.
2. **Leibniz** (`hasDerivAt_charFun_leibniz`): differentiate under the integral
   to bring down `i*w(f_0)`.

Equating via `HasDerivAt.unique` yields `gaussian_ibp`.

The general `gaussian_ibp_general` extends this by induction on n:
- **Base (n = 0)**: Leibniz + product rule on A(t) * B(t) where
  A(t) = inner(Tf\_0, T(t g\_0 + h)) and B(t) = integral exp(i w(t g\_0 + h)) d mu.
- **Step (n -> n+1)**: Factor prod\_{n+2} = prod\_{n+1} * w(g\_last),
  apply the IH with shifted spectral parameter t * g\_last + h,
  then differentiate at t = 0.

### Layer 3: Wick's theorem and bounds

`wick_recursive` specializes `gaussian_ibp_general` to h = 0, lifting
from C to R via `Complex.ofReal_injective`.

`wick_bound` follows by induction on n: apply `wick_recursive`, bound
each summand by Cauchy-Schwarz, and sum (n+1) identical bounds to get
the (n+1) * (n-1)!! = (n+1)!! recurrence.

## Fin combinatorics

The inductive step of `gaussian_ibp_general` requires careful Fin reindexing.
Key Mathlib lemmas used:

| Lemma | Role |
|---|---|
| `Fin.sum_univ_castSucc` | Split sum over Fin(n+2) into sum over Fin(n+1) + last |
| `Fin.prod_univ_castSucc` | Split prod over Fin(n+1) into prod over Fin(n) * last |
| `Fin.succAbove_last` | succAbove(last) = castSucc |
| `Fin.castSucc_succAbove_castSucc` | Commutation of castSucc with succAbove |
| `Fin.succAbove_ne_last_last` | a.succAbove(last n) = last(n+1) when a != last |
| `Fin.prod_univ_succAbove` | prod\_i f(i) = f(j) * prod\_{i != j} f(i) |

## Dependencies

- **Imports:** `GaussianField.Properties` (measure, charFun, moments, Lp bounds)
- **Mathlib:** `Nat.Factorial.DoubleFactorial`
- **Does not import:** `GaussianField.IsGaussian` (independent)

## References

- Janson, *Gaussian Hilbert Spaces*, Theorem 1.28
- Simon, *The P(phi)\_2 Euclidean (Quantum) Field Theory*, section I.3
- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*, section 6.1
