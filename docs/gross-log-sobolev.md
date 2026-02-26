# Gross Log-Sobolev Inequality

## Statement

For the centered Gaussian measure $\mu$ on the configuration space
$E' = \text{WeakDual}\ \mathbb{R}\ E$ with covariance
$C(f,g) = \langle T f, T g \rangle_H$, the entropy of $\omega(f)^2$ is
controlled by twice the variance:

$$\int \omega(f)^2 \log\!\left(\frac{\omega(f)^2}{\mathbb{E}[\omega(f)^2]}\right) d\mu \;\le\; 2\,\|T f\|^2$$

This is `gross_log_sobolev` in `GaussianField/Hypercontractive.lean`.

## Proof outline

### Reduction to one dimension

Since the integrand depends only on the single linear functional $\omega(f)$,
the infinite-dimensional integral reduces to a 1D Gaussian integral via
`pairing_is_gaussian`. With $\sigma^2 = \|Tf\|^2$ the problem becomes:

$$\int x^2 \log\!\left(\frac{x^2}{\sigma^2}\right) d\gamma_{0,\sigma^2}(x) \;\le\; 2\sigma^2$$

This is `log_sobolev_1d` in the same file.

### Pointwise bound

The key ingredient is `sq_log_div_le`: for all $x \in \mathbb{R}$ and
$\sigma^2 > 0$,

$$x^2 \log\!\left(\frac{x^2}{\sigma^2}\right) \;\le\; \frac{x^4}{\sigma^2} - x^2$$

This follows from $\log y \le y - 1$ (for $y > 0$) applied to
$y = x^2/\sigma^2$, then multiplied by $x^2$.

### Moment computation

Integrating the pointwise bound against $\gamma_{0,\sigma^2}$ gives

$$\text{LHS} \;\le\; \frac{\mathbb{E}[X^4]}{\sigma^2} - \mathbb{E}[X^2]
\;=\; \frac{3\sigma^4}{\sigma^2} - \sigma^2 \;=\; 2\sigma^2$$

using the Gaussian moments $\mathbb{E}[X^2] = \sigma^2$ and
$\mathbb{E}[X^4] = 3\sigma^4$.

The fourth moment identity $\mathbb{E}_{N(0,1)}[X^4] = 3$
(`fourth_moment_standard_gaussian`) is proved by computing the 4th
derivative of the moment generating function $e^{t^2/2}$ at $t = 0$ via
four explicit `HasDerivAt` steps. The general-variance result
$\mathbb{E}_{N(0,v)}[X^4] = 3v^2$ (`integral_pow4_gaussianReal`) follows
by scaling.

## File structure

All definitions and lemmas live in `GaussianField/Hypercontractive.lean`:

| Declaration | Role |
|-------------|------|
| `gaussian_abs_moment_std` | $\mathbb{E}_{N(0,1)}[\lvert Z\rvert^k]$ in terms of $\Gamma$ |
| `fourth_moment_standard_gaussian` | $\mathbb{E}_{N(0,1)}[Z^4] = 3$ via MGF |
| `sq_log_div_le` | Pointwise bound $x^2\log(x^2/\sigma^2) \le x^4/\sigma^2 - x^2$ |
| `integral_sq_gaussianReal` | $\mathbb{E}_{N(0,v)}[X^2] = v$ |
| `integral_pow4_gaussianReal` | $\mathbb{E}_{N(0,v)}[X^4] = 3v^2$ |
| `log_sobolev_1d` | 1D log-Sobolev for linear functions |
| `gross_log_sobolev` | Full infinite-dimensional theorem |

No axioms, no sorry.

## References

- L. Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975), 1061–1083
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Prop. I.16
