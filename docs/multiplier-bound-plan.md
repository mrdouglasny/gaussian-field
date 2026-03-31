# Plan: Prove resolventSchwartz_uniformBound

*Created 2026-03-31*

## Goal

Prove the axiom `resolventSchwartz_uniformBound` in `SchwartzFourier/ResolventUniformBound.lean:147`.
This is the single most impactful axiom to eliminate — it directly enables the cylinder mass operator
construction and provides infrastructure for the other cylinder axioms.

## The Blocker (RESOLVED)

Previous attempts stalled on "accessing pointwise evaluation through Mathlib's `fourierMultiplierCLM`."
This is now understood to be fully tractable:

- `fourierMultiplierCLM_apply` is **definitional** (`rfl`)
- The existing proof of `fourierMultiplier_preserves_real` (FourierMultiplier.lean:254-349)
  demonstrates the exact unwinding pattern
- All needed Mathlib lemmas exist: `postcompCLM_apply`, `smulLeftCLM_apply`,
  `fourier_coe`, `fourierInv_coe`, `fourierCLM_apply`, `fourierInvCLM_apply`

## Proof Plan

### Step 1: Pointwise evaluation lemma (new)

```
realFourierMultiplierCLM_apply_eq (σ : ℝ → ℝ) (hσ) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    (realFourierMultiplierCLM σ hσ f) x =
    Complex.re (FourierTransformInv.fourierInv
      (fun p => ↑(σ p) * FourierTransform.fourier (Complex.ofReal ∘ f) p) x)
```

**How:** Follow the pattern from `fourierMultiplier_preserves_real`:
```
simp only [realFourierMultiplierCLM, ContinuousLinearMap.comp_apply,
  schwartzToComplex, schwartzToReal, postcompCLM_apply,
  fourierMultiplierCLM_apply]
rw [Complex.reCLM_apply]
congr 1
-- bridge to function-level Fourier using fourier_coe, fourierInv_coe
```

### Step 2: Sup-norm bound for (0,0) case

Fill the sorry in `resolventMultiplier_sup_bound` (MultiplierBound.lean:153).

```
‖(R_ω f)(x)‖ = |re(F⁻¹(σ_ω · F(ofReal f))(x))|
             ≤ ‖F⁻¹(σ_ω · F(ofReal f))(x)‖     -- abs_re_le_abs
             ≤ ∫ ‖σ_ω(p) · (Ff)(p)‖ dp           -- norm_fourierInv_le_integral_norm
             ≤ ‖σ_ω‖_∞ · ∫ ‖Ff(p)‖ dp            -- pointwise bound + integral_mono
             ≤ (1/mass) · C · p(f)                 -- resolventSymbol_sup_uniform + schwartz_l1_le_seminorm
```

**Existing pieces:** `norm_fourierInv_le_integral_norm` (proved),
`resolventSymbol_sup_uniform` (proved), `schwartz_l1_le_seminorm` (proved).
Gap: connecting via Step 1's pointwise evaluation.

### Step 3: General (k,l) case

Fill `resolventSchwartz_uniformBound_direct` (MultiplierBound.lean:177).

The general Schwartz seminorm is `sup_x |x^k · D^l((R_ω f))(x)|`.
In the Fourier domain:
- `D^l(R_ω f) = F⁻¹((2πip)^l · σ_ω · Ff)`
- `x^k · F⁻¹(h)(x) = (2πi)^{-k} · F⁻¹(D^k_p h)(x)`

So: `p_{k,l}(R_ω f) ≤ C_k · ∫ |D^k_p((2πip)^l σ_ω · Ff)| dp`

Apply Leibniz with `A = p^l · σ_ω` and `B = Ff`:
`≤ C_k · Σ_j C(k,j) · ∫ |D^j(p^l σ_ω)| · |D^{k-j}(Ff)| dp`

**CRITICAL (Gemini correction):** `D^j(p^l σ_ω)` is NOT bounded in sup norm
when `l ≥ 1` — it grows like `|p|^{l-1}`. Instead use polynomial growth bound:

`|D^j(p^l σ_ω(p))| ≤ C_{j,l} · (1 + |p|)^{max(0, l-j-1)}`

uniformly in ω ≥ mass. This follows from:
- `|D^b(σ_ω)(p)| ≤ C'_b · (1+|p|)^{-1-b}` (uniform in ω, from scaling)
- Leibniz on `p^l · σ_ω`: each term `p^{l-m} · D^{j-m}(σ_ω)` grows like `|p|^{l-j-1}`

Then absorb the polynomial growth against the rapid decay of `D^{k-j}(Ff)`:
`∫ (1+|p|)^N · |D^{k-j}(Ff)(p)| dp ≤ C · q_{M, k-j}(Ff)`

for M large enough (choose M > N + 1). This is a Schwartz seminorm of Ff,
hence bounded by a seminorm of f.

**Sub-lemmas needed:**
1. Uniform polynomial growth bound for `D^j(p^l σ_ω)` (scaling argument)
2. Weighted L¹ bound for Schwartz functions: `∫ (1+|p|)^N |g| ≤ C · q(g)`
3. Leibniz rule for products (induction on k)

**Difficulty:** Hard but doable. Each sub-lemma is standard.

### Step 4: Package into the axiom

`resolventSchwartz_uniformBound` in ResolventUniformBound.lean follows from
`resolventSchwartz_uniformBound_direct` by packaging the (k,l)-dependent bound
into a single continuous seminorm via `Seminorm.bound_of_continuous`.

## Key Files

| File | Action |
|------|--------|
| `Cylinder/FourierMultiplier.lean` | Add `realFourierMultiplierCLM_apply_eq` |
| `SchwartzFourier/MultiplierBound.lean` | Fill 2 sorries using the new apply lemma |
| `SchwartzFourier/ResolventUniformBound.lean` | Replace axiom with proof |

## Reference: Unwinding Pattern

From `fourierMultiplier_preserves_real` (FourierMultiplier.lean:254-266):
```lean
ext f x
simp only [ContinuousLinearMap.comp_apply, schwartzToComplex, schwartzToReal,
  SchwartzMap.postcompCLM_apply, SchwartzMap.fourierMultiplierCLM_apply]
set g := SchwartzMap.smulLeftCLM ℂ σ (FourierTransform.fourier ...)
have hFI := congr_fun (SchwartzMap.fourierInv_coe g) x
rw [hFI]
simp only [SchwartzMap.smulLeftCLM_apply hσ]
```

## Estimated Effort

- Step 1: Small (30 min) — pattern already demonstrated
- Step 2: Medium (2-3 hours) — chain existing lemmas
- Step 3: Hard (1-2 days) — Leibniz rule induction
- Step 4: Small (30 min) — packaging

Step 2 alone gives the (0,0) case which is already useful.
