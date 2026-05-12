# `gff_wickPower_two_site_inner` — Codex implementation plan

## Goal

Discharge the single `sorry` in
`GaussianField/WickMultivariate.lean` at the bottom of the file
(declaration `gff_wickPower_two_site_inner`), without introducing
any new axioms or sorries.

## Statement

```lean
theorem gff_wickPower_two_site_inner
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (n m : ℕ) (x y : FinLatticeSites d N) :
    ∫ ω, wickMonomial n (gffSiteVariance d N a mass ha hmass x)
            (ω (Pi.single x 1)) *
          wickMonomial m (gffSiteVariance d N a mass ha hmass y)
            (ω (Pi.single y 1))
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    if n = m then
      (n.factorial : ℝ) * (gffPositionCovariance d N a mass x y) ^ n
    else 0
```

The Janson–Hilbert two-site Wick power formula, specialised to single-site
Wick monomials under the lattice GFF measure.

## Where this lives

- File: `GaussianField/WickMultivariate.lean`
- Section: `## 2-site Wick power formula on the lattice GFF`
- Just after `wickMonomial_at_site_eq_eigen_sum` (a private helper added
  alongside this stub)
- Inside `namespace GaussianField` (private/internal section after
  `siteWickMonomial_eigenbasis_expansion`)

## Why this matters

The formula is the analytical bottleneck for **two pphi2 sorries** on the
critical path of the `polynomial_chaos_exp_moment_bridge` discharge:

1. `pphi2/Pphi2/NelsonEstimate/RoughErrorBound.lean:407` —
   `canonicalCrossTerm_inner_eq_zero` (cross-term orthogonality, S3 of the
   `rough_error_variance` plan). Uses the **off-diagonal** `n ≠ m` case.
2. `pphi2/Pphi2/NelsonEstimate/RoughErrorBound.lean:852` —
   `canonicalCrossTerm_l2_sq_le` (per-cross-term L² bound, S4 of the
   `rough_error_variance` plan). Uses the **diagonal** `n = m` case to
   compute `∫ canonicalCrossTerm² dμ` explicitly.

After landing this lemma, bump `pphi2`'s `gaussian-field` pin and use it
in `pphi2`'s S3 + S4 work. See
`pphi2/docs/rough-error-variance-plan.md` for the upstream context.

## Math derivation (the "what's actually being proved")

Let `c_a(x) := gffSiteVariance d N a mass ha hmass x`.
Let `γ_j(x) := gffEigenCoeff d N a mass j x = e_j(x) / √(a^d λ_j)`.
Let `ξ_j(ω) := gffOrthonormalCoord d N a mass ha hmass j ω` (standard
Gaussian under the GFF pushforward).

Already proved in this file (private helpers):
- `gffSiteVariance_eq_sum_gamma_sq`: `c_a(x) = Σ_j γ_j(x)²`
- `omega_eval_delta_eq_sum_gamma_xi`: `ω(δ_x) = Σ_j γ_j(x) · ξ_j(ω)`

So
```
wickMonomial n c_a(x) (ω(δ_x))
  = wickMonomial n (Σ_j γ_j(x)²) (Σ_j γ_j(x) · ξ_j(ω)).
```
Apply `wickMonomial_pow_sum_expansion_of_totalDegree` (line 504, public):
```
  = Σ_{α : multiIndicesOfTotalDegree (FinLatticeSites d N) n}
      (n! / ∏_j α_j!) · (∏_j γ_j(x)^{α_j}) · ∏_j wickMonomial (α_j) 1 (ξ_j(ω))
  = Σ_α coef_n(α, x) · gffMultiWickMonomial α ω
```
where `coef_n(α, x) := (n!/∏α!) · ∏γ_j(x)^{α_j}` and the last step uses
the definition of `gffMultiWickMonomial` (line 111). This is exactly
`wickMonomial_at_site_eq_eigen_sum` (the private helper just added).

Multiply the `x` and `y` factors:
```
LHS integrand
  = (Σ_α coef_n(α, x) · gffMW α ω) · (Σ_β coef_m(β, y) · gffMW β ω)
  = Σ_{α, β} coef_n(α, x) · coef_m(β, y) · gffMW α ω · gffMW β ω.
```

Integrate (linearity of integration over a finite double sum; see
"Integrability" below):
```
∫ LHS = Σ_{α, β} coef_n(α, x) · coef_m(β, y) · ∫ gffMW α ω · gffMW β ω dμ
```

Apply `gffMultiWickMonomial_orthogonality` (line 210, public):
```
∫ gffMW α · gffMW β dμ = if α = β then (∏_k α_k!) else 0
```

So
```
∫ LHS = Σ_{α : |α|=n} Σ_{β : |β|=m}
          coef_n(α, x) · coef_m(β, y) · (if α = β then ∏_k α_k! else 0).
```

The inner sum collapses to the `α = β` case, which requires
`α ∈ multiIndicesOfTotalDegree _ m` AND `α ∈ multiIndicesOfTotalDegree _ n`.
Equivalently, `|α| = n = m`.

- **Case `n ≠ m`:** no `α` satisfies both, so all summands are 0. ✓
- **Case `n = m`:** the inner sum collapses to a single term per `α`:
  ```
  ∫ LHS = Σ_{|α|=n} coef_n(α, x) · coef_n(α, y) · ∏_k α_k!
        = Σ_{|α|=n} (n!/∏α!) · (n!/∏α!) · (∏γ_j(x)^{α_j}) · (∏γ_j(y)^{α_j}) · ∏α_k!
        = Σ_{|α|=n} (n!)² / (∏α!) · ∏ (γ_j(x) · γ_j(y))^{α_j}     [(∏α!)² · (1/∏α!) = ∏α!]
        = n! · Σ_{|α|=n} (n!/∏α!) · ∏ (γ_j(x) · γ_j(y))^{α_j}
        = n! · (Σ_j γ_j(x) · γ_j(y))^n              [multinomial theorem]
        = n! · gffPositionCovariance(x, y)^n.       [defn]
  ```
  Final equality matches the RHS `if n = m then n! · C(x,y)^n else 0`. ✓

The single piece of "real new mathematical content" is the **multinomial
theorem** in the form
```
(Σ_j a_j)^n = Σ_{|α|=n} (n! / ∏α!) · ∏ a_j^{α_j}
```
applied with `a_j := γ_j(x) · γ_j(y)`. See "Multinomial theorem" below.

## Step-by-step proof plan

### Step 1 — Substitute the eigenbasis expansion

Apply `wickMonomial_at_site_eq_eigen_sum` to both Wick monomial factors.
Concrete:

```lean
have h_integrand : ∀ ω : Configuration (FinLatticeField d N),
  wickMonomial n (gffSiteVariance d N a mass ha hmass x) (ω (Pi.single x 1)) *
  wickMonomial m (gffSiteVariance d N a mass ha hmass y) (ω (Pi.single y 1)) =
  (∑ α ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) n,
    ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
      (∏ j, gffEigenCoeff d N a mass j x ^ (α j)) *
      gffMultiWickMonomial d N a mass ha hmass α ω) *
  (∑ β ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) m,
    ((m.factorial : ℝ) / ∏ j, ((β j).factorial : ℝ)) *
      (∏ j, gffEigenCoeff d N a mass j y ^ (β j)) *
      gffMultiWickMonomial d N a mass ha hmass β ω) := by
  intro ω
  rw [wickMonomial_at_site_eq_eigen_sum d N a mass ha hmass n x ω,
      wickMonomial_at_site_eq_eigen_sum d N a mass ha hmass m y ω]
simp_rw [h_integrand]
```

After this, the integrand is a product of two finite sums.

### Step 2 — Distribute via `Finset.sum_mul_sum`

```lean
have h_distribute : ∀ ω,
  (∑ α ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) n,
    coef_n(α, x) · gffMultiWickMonomial d N a mass ha hmass α ω) *
  (∑ β ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) m,
    coef_m(β, y) · gffMultiWickMonomial d N a mass ha hmass β ω) =
  ∑ α ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) n,
    ∑ β ∈ multiIndicesOfTotalDegree (FinLatticeSites d N) m,
      (coef_n(α, x) · coef_m(β, y)) *
        (gffMultiWickMonomial d N a mass ha hmass α ω *
         gffMultiWickMonomial d N a mass ha hmass β ω) := by
  intros
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  refine Finset.sum_congr rfl fun β _ => ?_
  ring
simp_rw [h_distribute]
```

(Inline the `coef_n` / `coef_m` definitions — they're not separate `def`s.)

### Step 3 — Integration linearity (twice)

Use `MeasureTheory.integral_finset_sum` to swap `∫` with the outer and
inner finite sums. Requires integrability hypotheses for each summand.

The summand for fixed `(α, β)` is
```
(coef_n(α, x) · coef_m(β, y)) ·
  (gffMultiWickMonomial α ω · gffMultiWickMonomial β ω)
```
which is a constant times a continuous function of `ω` (each
`gffMultiWickMonomial` is a finite product of polynomials in continuous
evaluations `gffOrthonormalCoord`). Since `latticeGaussianMeasure` is a
probability measure (hence finite), continuous functions are integrable.

Use `Continuous.integrable` (or its specialisation
`Continuous.integrable_of_isFiniteMeasure` / probability-measure variant
in Mathlib) to discharge integrability. The continuity of
`gffMultiWickMonomial α` follows from `Continuous.finset_prod`.

```lean
have h_int : ∀ α β,
    Integrable (fun ω => (coef_n α x · coef_m β y) *
      (gffMultiWickMonomial d N a mass ha hmass α ω *
       gffMultiWickMonomial d N a mass ha hmass β ω))
      (latticeGaussianMeasure d N a mass ha hmass) := by
  intros α β
  refine Continuous.integrable_of_isFiniteMeasure ?_
  exact continuous_const.mul ((continuous_gffMultiWickMonomial _ _ _ _ _ _ α).mul
    (continuous_gffMultiWickMonomial _ _ _ _ _ _ β))
```

(May need to add a helper `continuous_gffMultiWickMonomial` first; mirror
the continuity argument inside `gffMultiWickMonomial_orthogonality` proof
at line 244.)

After integration linearity:
```
∫ Σ_α Σ_β (...) dμ
  = Σ_α Σ_β ∫ (coef_n α x · coef_m β y) · (gffMW α ω · gffMW β ω) dμ
  = Σ_α Σ_β (coef_n α x · coef_m β y) · ∫ gffMW α ω · gffMW β ω dμ
```
(via `MeasureTheory.integral_const_mul` for the constant pull-out).

### Step 4 — Apply `gffMultiWickMonomial_orthogonality`

```lean
simp_rw [gffMultiWickMonomial_orthogonality d N a mass ha hmass]
```
Each `∫ gffMW α · gffMW β dμ` becomes `if α = β then ∏_k α_k! else 0`.

### Step 5 — Branch on `n = m`

```lean
split_ifs with h_eq
```

#### Case `n ≠ m` (the easy branch):

The inner sum is
```
Σ_{β ∈ multiIndicesOfTotalDegree _ m}
  (coef_n α x · coef_m β y) · (if α = β then ∏β_k! else 0)
```
For this to be non-zero we'd need `α = β`, hence `α ∈ multiIndicesOfTotalDegree _ m`,
which combined with `α ∈ multiIndicesOfTotalDegree _ n` (from the outer
sum) gives `|α| = n` and `|α| = m`, contradicting `n ≠ m`.

Concrete tactic:
```lean
apply Finset.sum_eq_zero
intros α hα
apply Finset.sum_eq_zero
intros β hβ
-- Goal: (coef_n α x · coef_m β y) · (if α = β then ∏β_k! else 0) = 0
by_cases h_αβ : α = β
· -- α = β: but α has total degree n and β has total degree m, contradiction
  subst h_αβ
  rw [Finset.mem_filter] at hα hβ
  -- hα.2 : Σ α j = n, hβ.2 : Σ α j = m, so n = m, contradiction
  exact absurd (hα.2.symm.trans hβ.2) h_eq
· rw [if_neg h_αβ, mul_zero]
```

(`multiIndicesOfTotalDegree` is `(piFinset (range (k+1))).filter (·.sum = k)`.
Use `Finset.mem_filter` to extract the degree.)

#### Case `n = m` (the hard branch):

Substitute `m = n`. The double sum collapses (via `Finset.sum_ite_eq'` or
similar diagonal-sum lemma) to a single sum over `α ∈ multiIndicesOfTotalDegree _ n`:

```lean
subst h_eq
-- Goal: Σ_α Σ_β (coef_n α x · coef_n β y) · (if α = β then ∏β_k! else 0) =
--       n! · gffPositionCovariance(x, y)^n
```

Reorder/collapse to:
```
Σ_{α ∈ multiIndicesOfTotalDegree _ n}
  (coef_n α x · coef_n α y) · ∏α_k!
```

Substitute `coef_n α x = (n!/∏α!) · ∏γ_j(x)^{α_j}`:
```
= Σ_α [(n!/∏α!) · ∏γ_j(x)^{α_j}] · [(n!/∏α!) · ∏γ_j(y)^{α_j}] · ∏α_k!
= Σ_α (n!)² / (∏α!) · ∏(γ_j(x) · γ_j(y))^{α_j}        -- algebra
= n! · Σ_α (n!/∏α!) · ∏(γ_j(x) · γ_j(y))^{α_j}
```

Now apply the **multinomial theorem** (see below) with `a_j := γ_j(x) · γ_j(y)`:
```
Σ_{|α|=n} (n!/∏α!) · ∏ a_j^{α_j} = (Σ_j a_j)^n
```

Substitute `Σ_j γ_j(x) · γ_j(y) = gffPositionCovariance(x, y)` (by `def`).

Result: `n! · gffPositionCovariance(x, y)^n`. ✓

## Multinomial theorem dependency

Look in Mathlib for the multinomial theorem in the form
```
(∑ j ∈ Finset.univ, a j) ^ n =
  ∑ α ∈ multiIndicesOfTotalDegree ι n,
    ((n.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) * ∏ j, a j ^ (α j)
```

Candidates to search (use `lean_loogle` / `lean_leansearch` / `Grep`):
- `Finset.sum_pow_mul_eq_..`
- `Multinomial.sum_pow`
- `Nat.multinomial`
- `Polynomial.eval_sum_pow_..`

If Mathlib does NOT have it in this form, prove it directly (~50 lines) by
induction on the support `Finset.univ` of `ι`, peeling off one index at a
time and using the binomial theorem (`add_pow`) inductively. The
analogue for `wickMonomial` already exists as
`wickMonomial_pow_sum_expansion_of_totalDegree` (line 504); the
multinomial theorem reduces to that proof structure with `c = 0` (no Wick
subtraction).

In fact, **the cleanest specialisation route** may be: use
`wickMonomial_pow_sum_expansion_of_totalDegree` itself with `γ_j := a_j`
and `ξ_j := 1`, then `wickMonomial k 0 1 = 1` for `k = 0` and we collapse
the per-coordinate factors. Worth checking before re-deriving.

## Integrability dependency

For Step 3, integrability of each `gffMultiWickMonomial α` and pairwise
products. All are continuous functions (finite products of polynomials in
continuous coordinate evaluations on a Polish space) and the GFF measure
is a probability measure (finite). So `Continuous.integrable_of_isFiniteMeasure`
applies.

The continuity argument is implicit inside the proof of
`gffMultiWickMonomial_orthogonality` (line 244 of WickMultivariate.lean —
look for `h_strong_meas`/`h_wick_cont`/`continuous_finset_prod`). May want
to extract it as a public `continuous_gffMultiWickMonomial` lemma first.

## Acceptance criteria

- `lake build` clean from scratch on the
  `gaussian-field` `main` branch.
- `#print axioms gff_wickPower_two_site_inner` shows only the standard
  Mathlib trio (`propext`, `Classical.choice`, `Quot.sound`).
- No new sorries anywhere in `gaussian-field`.
- No new axioms anywhere in `gaussian-field` (the existing axiom count
  should stay the same).

## After landing

1. Push to `gaussian-field` `main`.
2. In `pphi2`, bump the gaussian-field pin in `lake-manifest.json`
   (`lake update GaussianField`).
3. Discharge the two pphi2 sorries:
   - `canonicalCrossTerm_inner_eq_zero`
     (`pphi2/Pphi2/NelsonEstimate/RoughErrorBound.lean:407`): use
     `MeasureTheory.integral_prod_mul` to factor the joint-measure
     integral into smooth × rough, then apply
     `gff_wickPower_two_site_inner` to each factor with `n ≠ m` cases.
   - `canonicalCrossTerm_l2_sq_le`
     (`pphi2/Pphi2/NelsonEstimate/RoughErrorBound.lean:852`): use the
     diagonal `n = m` case to compute `∫ canonicalCrossTerm² dμ` explicitly
     in terms of `gffPositionCovariance` powers, then bound via the upstream
     Glimm-Jaffe Fourier estimates (Phase B work).
4. Update `pphi2/docs/AXIOM_STATUS.md` to reflect the discharged sorries.

## Hand-off note

Codex: please flag exact signatures of any helper lemmas you need to add
(continuity helper, multinomial theorem, integrability), and any
encountered Mathlib API mismatches. The proof structure is laid out
above; the analytic content is genuinely contained in the multinomial
step and the continuity helper.
