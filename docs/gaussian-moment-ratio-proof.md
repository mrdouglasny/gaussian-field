# Hypercontractive Estimate via Double Factorials

## Overview

Nelson's hypercontractive estimate for the standard Gaussian states:

$$\mathbb{E}[|Z|^{pn}] \le (p-1)^{pn/2} \, \mathbb{E}[|Z|^{2n}]^{p/2}$$

For even integer $p = 2m$, this is proved entirely by combinatorics on
double factorials in `GaussianField/HypercontractiveNat.lean`, with no
axioms, no Gamma function calculus, and no sorry.

The full chain (`hypercontractive_1d`, `hypercontractive_gaussianReal`,
`gaussian_hypercontractive`) lives in `HypercontractiveNat.lean` with
hypotheses `(m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m)`.

The Gross log-Sobolev inequality `gross_log_sobolev` in
`Hypercontractive.lean` is proved independently (via E[X⁴] = 3σ⁴ and
log(y) ≤ y − 1) and does not depend on the hypercontractive chain.

## File structure

| File | Contents |
|------|----------|
| `Hypercontractive.lean` | Gaussian absolute moments via Gamma, log-Sobolev inequality |
| `HypercontractiveNat.lean` | Double-factorial bridge, combinatorial inequality, hypercontractive chain |

---

## The combinatorial proof

For $p = 2m$, the Gaussian moments are double factorials:

$$\mathbb{E}[Z^{2k}] = (2k-1)!!$$

The hypercontractive inequality reduces to a purely discrete statement:

$$(2mn - 1)!! \le (2m-1)^{mn} \cdot ((2n-1)!!)^m$$

### Proof sketch

The LHS is $\prod_{k=0}^{mn-1}(2k+1)$.

1. **Partition** into $n$ blocks of $m$ terms via `prod_repartition`.
2. **Bound each block**: every term $2(mi + j) + 1$ in block $i$
   satisfies $2(mi+j)+1 \le (2m-1)(2i+1)$ (`block_element_bound`).
3. **Each block product** $\le ((2m-1)(2i+1))^m$ (`block_prod_bound`).
4. **Recombine** via `Finset.prod_mul_distrib` and `Finset.prod_pow`
   to get $(2m-1)^{mn} \cdot \prod_{i=0}^{n-1}(2i+1)^m = (2m-1)^{mn} \cdot ((2n-1)!!)^m$.

### Bridge to Gaussian moments

`gaussian_even_moment_eq_doubleFactorial` converts $\mathbb{E}[|Z|^{2n}]$
to $(2n-1)!!$ using Mathlib's `Real.Gamma_nat_add_half`:

$$\Gamma(n + \tfrac{1}{2}) = (2n-1)!! \cdot \sqrt{\pi} / 2^n$$

### Lifting to general variance and infinite dimensions

- `hypercontractive_1d`: wraps the ℕ-power result into rpow form
  via `subst` + `rpow_natCast`
- `hypercontractive_gaussianReal`: scales from N(0,1) to N(0,v)
  via $\sigma = \sqrt{v}$
- `gaussian_hypercontractive`: pushes forward through
  `pairing_is_gaussian` to the infinite-dimensional Gaussian field

---

## The general real p case (not formalized)

For real $p \ge 2$, the most elegant approach (Weissler) derives the
inequality from the 1D Gross log-Sobolev inequality via an ODE:

$$\frac{d}{dq}\!\left(\frac{\log M(q)}{q}\right) \le \frac{1}{2(q-1)}$$

where $M(q) = \mathbb{E}[|Z|^q]$. Integrating from $2n$ to $pn$ gives the
bound. This requires differentiation under the integral sign and is blocked
on Digamma/Trigamma infrastructure not yet in Mathlib.

---

## References

- Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory*, Theorem I.17
- Glimm–Jaffe, *Quantum Physics*, Ch. 8
- Weissler, *Logarithmic Sobolev inequalities and hypercontractive estimates
  on the circle*, J. Funct. Anal. (1979)
