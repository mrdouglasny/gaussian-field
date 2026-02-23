# Wick's Theorem (Isserlis' Theorem)

**File:** [`GaussianField/Wick.lean`](../GaussianField/Wick.lean) (1,067 lines, sorry-free)

Wick's theorem expresses the $n$-point functions of a centered Gaussian measure
in terms of the 2-point function (covariance). This is the combinatorial heart
of free-field QFT, and is also known as Isserlis' theorem in probability.

## Main results

### Gaussian integration by parts

**`gaussian_ibp`** — Base case. For a single evaluation functional times the
characteristic exponential:

$$\mathbb{E}\bigl[\omega(f_0)\,e^{i\omega(h)}\bigr]
= i\,\langle Tf_0,\,Th\rangle\;\mathbb{E}\bigl[e^{i\omega(h)}\bigr]$$

**`gaussian_ibp_general`** — Full inductive version with polynomial weight.
For $n+1$ test functions $g_0,\ldots,g_n$ and a "spectral parameter" $h$:

$$\mathbb{E}\Bigl[\omega(f_0)\prod_{i=0}^n \omega(g_i)\,e^{i\omega(h)}\Bigr]
= \sum_{j=0}^n \langle Tf_0,\,Tg_j\rangle\;\mathbb{E}\Bigl[\prod_{i\neq j}\omega(g_i)\,e^{i\omega(h)}\Bigr]
+ i\,\langle Tf_0,\,Th\rangle\;\mathbb{E}\Bigl[\prod_i\omega(g_i)\,e^{i\omega(h)}\Bigr]$$

The $e^{i\omega(h)}$ factor is the Fourier-analytic handle that drives the induction:
differentiating with respect to a parameter $t$ in $e^{i\omega(t\cdot g + h)}$
brings down $i\,\omega(g)$ factors, relating the $(n+1)$-point integral to $n$-point integrals.

### Wick's recursive formula

**`wick_recursive`** — Setting $h = 0$ in `gaussian_ibp_general` kills the
exponential ($e^0 = 1$) and the last term ($\langle Tf_0, T(0)\rangle = 0$),
giving the purely polynomial identity:

$$\mathbb{E}\Bigl[\omega(f_0)\prod_{i=0}^n\omega(g_i)\Bigr]
= \sum_{j=0}^n \langle Tf_0,\,Tg_j\rangle\;\mathbb{E}\Bigl[\prod_{i\neq j}\omega(g_i)\Bigr]$$

This is Wick's theorem in recursive form: pick a partner $g_j$ for $f_0$,
extract the covariance $\langle Tf_0, Tg_j\rangle$, and recurse on the remaining variables.

### Odd moments vanish

**`odd_moment_vanish`** — For a centered Gaussian measure, all odd moments are zero:

$$\mathbb{E}\Bigl[\prod_{i=0}^{2k}\omega(f_i)\Bigr] = 0$$

Proof by induction on $k$: `wick_recursive` expresses the $(2k+1)$-point function
as a sum of $(2k-1)$-point functions, which vanish by the inductive hypothesis.

### Wick bound

**`wick_bound`** — Bound on $n$-point functions:

$$\Bigl|\mathbb{E}\Bigl[\prod_{i=0}^{n-1}\omega(f_i)\Bigr]\Bigr|
\le (n-1)!!\;\prod_i \|T(f_i)\|$$

Proof by induction using `wick_recursive` and Cauchy-Schwarz at each step.
The $(n-1)!!$ factor counts the number of perfect pairings of $n$ elements.

**`wick_bound_factorial`** — Factorial form suitable for OS1':

$$\Bigl|\mathbb{E}\Bigl[\prod_i\omega(f_i)\Bigr]\Bigr|
\le \sqrt{n!}\;\prod_i \|T(f_i)\|$$

Uses the auxiliary lemma `double_factorial_le_sqrt_factorial`: $(n-1)!! \le \sqrt{n!}$.

## Lean API reference

| Definition / Theorem | Signature | Description |
|---|---|---|
| `product_integrable` | `Integrable (fun ω => ∏ i, ω (f i)) (measure T)` | Products of evaluation functionals are integrable |
| `gaussian_ibp` | integral identity | IBP for single evaluation × exponential |
| `gaussian_ibp_general` | integral identity | IBP for polynomial × exponential |
| `wick_recursive` | integral identity | Recursive Wick formula ($h = 0$ specialization) |
| `odd_moment_vanish` | `∫ ω, ∏ i, ω (f i) ∂(measure T) = 0` | Odd moments vanish |
| `wick_bound` | norm bound | $(n-1)!!$ bound on $n$-point functions |
| `wick_bound_factorial` | norm bound | $\sqrt{n!}$ bound on $n$-point functions |
| `double_factorial_le_sqrt_factorial` | `((n-1)!! : ℝ) ≤ n!^{1/2}` | Auxiliary inequality |

## Proof architecture

The proof is organized in three layers:

### Layer 1: Differentiation under the integral

**`hasDerivAt_weighted_exp_leibniz`** — Leibniz rule for
$\frac{d}{dt}\big|_{t=0} \int P(\omega)\,e^{i\omega(t\cdot g + h)}\,d\mu$.

The polynomial weight $P(\omega)$ is constant in $t$, so the derivative at
$t = 0$ simply brings down $i\,\omega(g)$ from the exponential. Domination
is by $\|P(\omega)\| \cdot \|\omega(g)\|$, integrable when $P$ is a product
of evaluation functionals (via Hölder escalation in `product_integrable`).

### Layer 2: Gaussian IBP by characteristic functional

The base `gaussian_ibp` follows from differentiating the characteristic
functional $\mathbb{E}[e^{i\omega(f)}] = e^{-\frac{1}{2}\|Tf\|^2}$ in two ways:

1. **Closed form** (`hasDerivAt_charFun_closed`): differentiate the Gaussian
   $e^{-\frac{1}{2}\|T(t f_0 + h)\|^2}$ directly.
2. **Leibniz** (`hasDerivAt_charFun_leibniz`): differentiate under the integral
   to bring down $i\,\omega(f_0)$.

Equating via `HasDerivAt.unique` yields `gaussian_ibp`.

The general `gaussian_ibp_general` extends this by induction on $n$:
- **Base ($n = 0$)**: Leibniz + product rule on $A(t) \cdot B(t)$ where
  $A(t) = \langle Tf_0, T(tg_0 + h)\rangle$ and $B(t) = \int e^{i\omega(tg_0+h)} d\mu$.
- **Step ($n \to n+1$)**: Factor $\prod_{n+2} = \prod_{n+1} \cdot \omega(g_{\text{last}})$,
  apply the IH with shifted spectral parameter $t \cdot g_{\text{last}} + h$,
  then differentiate at $t = 0$.

### Layer 3: Wick's theorem and bounds

`wick_recursive` specializes `gaussian_ibp_general` to $h = 0$, lifting
from $\mathbb{C}$ to $\mathbb{R}$ via `Complex.ofReal_injective`.

`wick_bound` follows by induction on $n$: apply `wick_recursive`, bound
each summand by Cauchy-Schwarz, and sum $(n+1)$ identical bounds to get
the $(n+1) \cdot (n-1)!! = (n+1)!!$ recurrence.

## Fin combinatorics

The inductive step of `gaussian_ibp_general` requires careful Fin reindexing.
Key Mathlib lemmas used:

| Lemma | Role |
|---|---|
| `Fin.sum_univ_castSucc` | Split $\sum_{\text{Fin}(n+2)}$ into $\sum_{\text{Fin}(n+1)} + \text{last}$ |
| `Fin.prod_univ_castSucc` | Split $\prod_{\text{Fin}(n+1)}$ into $\prod_{\text{Fin}(n)} \cdot \text{last}$ |
| `Fin.succAbove_last` | $\text{succAbove}(\text{last}) = \text{castSucc}$ |
| `Fin.castSucc_succAbove_castSucc` | Commutation of castSucc with succAbove |
| `Fin.succAbove_ne_last_last` | $a.\text{succAbove}(\text{last}(n)) = \text{last}(n+1)$ when $a \ne \text{last}$ |
| `Fin.prod_univ_succAbove` | $\prod_i f(i) = f(j) \cdot \prod_{i \ne j} f(i)$ |

## Dependencies

- **Imports:** `GaussianField.Properties` (measure, charFun, moments, $L^p$ bounds)
- **Mathlib:** `Nat.Factorial.DoubleFactorial`
- **Does not import:** `GaussianField.IsGaussian` (independent)

## References

- Janson, *Gaussian Hilbert Spaces*, Theorem 1.28
- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, §I.3
- Glimm-Jaffe, *Quantum Physics: A Functional Integral Point of View*, §6.1
