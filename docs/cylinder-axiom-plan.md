# Plan: Three General Theorems to Prove Cylinder Axioms

## Context

The cylinder branch of gaussian-field has 5 active axioms (plus 2 sorries in MultiplierBound.lean). Three general theorems from functional/harmonic analysis would prove 4 of the 5 axioms, leaving only `resolvent_laplace_inner` (which is already a clean, elementary axiom).

## Gemini Review Summary

All three theorems vetted as mathematically correct. Key feedback:
- **Theorem 1:** Approach confirmed standard and clean
- **Theorem 2:** Square root step (S commutes with B → commutes with √B) requires functional calculus, non-trivial. Alternative approach (S isometry → G-invariance) simpler and sufficient for our use cases (translations, reflections are all isometries)
- **Theorem 3:** CRITICAL — must target DM basis ℓ² norm (weighted Fourier coefficients), not raw L² norm. The `l2InnerProduct` uses DM/Schauder basis coefficients which may include Sobolev-type weights

## Theorem 1: Uniform Fourier Multiplier Bounds on Schwartz Space

**Proves:** Axiom `resolventSchwartz_uniformBound` (SchwartzFourier/ResolventUniformBound.lean:147)

**Statement:** For a family of symbols `{σ_ω}_{ω≥mass}` with uniform derivative bounds `sup_{ω,p} |∂^k σ_ω(p)| ≤ B_k`, the Fourier multipliers `M_{σ_ω}` satisfy uniform Schwartz seminorm bounds.

**Existing infrastructure:**
- `realFourierMultiplierCLM` defined via Mathlib's `fourierMultiplierCLM` (Cylinder/FourierMultiplier.lean:216)
- `resolventSymbol_hasTemperateGrowth` proved (Cylinder/FourierMultiplier.lean:152)
- `resolventSymbol_sup_uniform` proved: `|σ_ω(p)| ≤ 1/mass` (Cylinder/FourierMultiplier.lean:123)
- Scaling identity `σ_ω(p) = ω⁻¹g(p/ω)` proved in SchwartzFourier/MultiplierBound.lean

**Implementation plan:**
1. **New file `SchwartzFourier/MultiplierSeminormBound.lean`** — General multiplier seminorm theorem
2. Prove: For Schwartz `f` and smooth symbol `σ` with `|∂^k σ| ≤ B_k`:
   - `p_{k,l}(M_σ f) ≤ C(B_0,...,B_{k+l}) · q_{k',l'}(f)` for suitable Schwartz seminorms
   - This follows from the Leibniz rule: `x^l ∂^k(F⁻¹(σ·Ff))` involves derivatives of σ times Schwartz seminorms of f
3. Apply to the resolvent family: scaling `σ_ω(p) = ω⁻¹g(p/ω)` gives `|∂^j σ_ω| ≤ mass^{-(j+1)} · |∂^j g|_∞`, all uniform in ω ≥ mass
4. Conclude `resolventSchwartz_uniformBound`

**Difficulty:** Medium. The Leibniz rule for Fourier multipliers is standard but requires careful bookkeeping with Schwartz seminorms. The main challenge is working through Mathlib's `fourierMultiplierCLM` API (lift-apply-project chain).

**Key files to modify:**
- `SchwartzFourier/MultiplierBound.lean` (extend existing work)
- `SchwartzFourier/ResolventUniformBound.lean` (replace axiom with proof)

---

## Theorem 2: Semigroup Commutation → Quadratic Form Preservation

**Proves:** Axiom `cylinderMassOperator_equivariant_of_heat_comm` (Cylinder/GreenFunction.lean:277)

**Statement:** If a CLM `S` commutes with `e^{-tA}` for all t ≥ 0, and `T = A^{-1/2}` maps test functions to ℓ², then `T ∘ S = U ∘ T` for some linear isometry `U` on ℓ².

**Existing infrastructure:**
- Mass operator T constructed mode-by-mode (NOT via spectral theory) in Cylinder/MassOperatorConstruction.lean
- Heat semigroup = `e^{-m²t} · (circleHeat ⊗ freeHeat)` in Cylinder/FreeHeatSemigroup.lean
- Heat commutation theorems proved for spatial/time translation and time reflection
- Mathlib has Bochner integral but NOT functional calculus for unbounded self-adjoint operators on real Hilbert spaces

**Implementation plan:**
1. **Mode-by-mode approach** (avoids spectral theory entirely):
   - S commutes with heat semigroup → S commutes with each mode's heat operator `e^{-tω²_a}·heatMultiplier_t`
   - At the mode level: S commutes with the 1D resolvent multiplier R_{ω_a} (since R_ω² is the Laplace transform of the heat kernel)
   - Therefore: `coeff_b(R_ω(slice_a(Sf))) = coeff_b(R_ω(S_a(slice_a f)))` where S_a is S restricted to mode a
   - The map U sends `(Tf)_{pair(a,b)}` to `(T(Sf))_{pair(a,b)}` and preserves the ℓ² norm because S preserves each mode's L² norm
2. **Key sub-lemma:** S commuting with heat semigroup implies S commuting with the resolvent multiplier R_ω for each ω. This uses `R_ω² = ∫₀^∞ e^{-tω²} · heatMultiplier_t dt` (Bochner integral of the heat semigroup).
3. **Isometry construction:** U is defined coordinate-wise using the mode decomposition. The ℓ² norm is preserved because S is an isometry on each mode's contribution.

**Difficulty:** Hard. The Bochner integral step `R_ω² = ∫ e^{-t} heatMult_{t/ω²} dt` requires Bochner integral theory for CLM-valued functions. The isometry construction requires showing the coordinate-wise map extends to ℓ².

**Recommended approach (per Gemini):** Since all actual uses (spatial/time translation, time reflection) have S as an isometry on test functions, use the simpler alternative:
1. S commutes with e^{-tA} and S preserves L²-type norms
2. G(Sf,Sf) = ∫₀^∞ ⟨Sf, e^{-tA}Sf⟩ dt = ∫₀^∞ ⟨f, S* e^{-tA} S f⟩ dt = ∫₀^∞ ⟨f, e^{-tA}f⟩ dt = G(f,f)
3. ‖T(Sf)‖² = G(Sf,Sf) = G(f,f) = ‖Tf‖², so the map U: Tf ↦ T(Sf) is an isometry
4. Extend U to ℓ² by density + BLT theorem

This avoids the functional calculus square root lemma entirely. The trade-off: the axiom statement requires the intertwining relation T(Sf) = U(Tf), not just isometry. But isometry of U + linearity gives the full intertwining since U is defined as Tf ↦ T(Sf).

**Note:** The full functional calculus approach (S commutes with √B) is more general but needs Mathlib infrastructure that doesn't exist yet. The isometry approach suffices for all current and foreseeable uses.

**Key files to modify:**
- `Cylinder/GreenFunction.lean` (replace axiom with proof)
- May need Bochner integral commutation lemma

---

## Theorem 3: Uniform Periodization Bound via Poisson Summation

**Proves:** Axiom `embed_l2_uniform_bound` (Cylinder/MethodOfImages.lean:326)

**Statement:** The ℓ² norm of a periodized Schwartz function (via method of images embedding into the torus) is bounded by a continuous Schwartz seminorm, uniformly in period L ≥ 1.

**Existing infrastructure:**
- `periodizeCLM` defined and continuous (SchwartzNuclear/Periodization.lean:730)
- `l2InnerProduct_pure`, `l2InnerProduct_swap`, `l2InnerProduct_le_seminorm` all proved (Cylinder/MethodOfImages.lean)
- Mathlib has `SchwartzMap.tsum_eq_tsum_fourier` — Poisson summation for Schwartz functions (no hypotheses needed)
- `periodize_sobolevSeminorm_le` — Sobolev seminorms of periodized function bounded by Schwartz seminorms

**Implementation plan:**
1. **Prove `periodize_l2_uniform_bound`** — For 1D Schwartz h:
   - ‖periodize_L h‖²_{L²[0,L]} = (1/L) Σ_k |F[h](2πk/L)|² (by Poisson + Parseval)
   - Since F[h] ∈ S(ℝ): |F[h](ξ)|² ≤ C·q(h)²·(1+|ξ|)^{-4} for a Schwartz seminorm q
   - The sum (1/L) Σ_k (1+|2πk/L|)^{-4} is bounded for L ≥ 1 (Riemann sum → integral)
   - Therefore: ‖periodize_L h‖²_{L²} ≤ C'·q(h)², uniformly in L ≥ 1
2. **Lift to tensor products** — For pure tensor g ⊗ h:
   - l2(embed(g⊗h)) = l2(g) · l2(periodize h) (by `l2InnerProduct_pure` + `l2InnerProduct_swap`)
   - ≤ q_g(g)² · C' · q_h(h)²
   - ≤ Q(g⊗h)² for a combined seminorm Q
3. **Extend to general f** by DM basis expansion + decay

**CRITICAL issue (flagged by Gemini):** The `l2InnerProduct` in the axiom uses DM basis coefficients, NOT raw L² inner product. For `SmoothMap_Circle L ℝ`, the DM basis may include Sobolev-type weights. Must verify:
- What is the DM basis for `SmoothMap_Circle L ℝ`? (Likely Fourier modes with Sobolev weighting)
- Does `l2InnerProduct` = `∑ coeff_m(f) * coeff_m(g)` where coeff_m are DM coefficients?
- If weighted: the Poisson summation argument still works but targets `∑ w_k |c_k|²` instead of `∑ |c_k|²`

**Revised proof strategy:**
1. Poisson summation gives Fourier coefficients `c_k = (1/L)F[h](2πk/L)`
2. DM coefficients `coeff_m` relate to Fourier coefficients via the DM basis (Fourier modes with normalization)
3. Bound `∑_m |coeff_m(periodize h)|²` by rapid decay of `F[h]` at the sample points
4. The sum `(1/L²) ∑_k w_k |F[h](2πk/L)|^{-2N}` for N large is uniformly bounded for L ≥ 1

**Difficulty:** Medium, but requires understanding the exact DM basis for `SmoothMap_Circle`. The Poisson summation step uses existing Mathlib infrastructure.

**Key files to modify:**
- `SchwartzNuclear/Periodization.lean` — Add uniform L² bound for periodization
- `Cylinder/MethodOfImages.lean` (replace axiom with proof)

---

## Priority Order

1. **Theorem 3 (Periodization)** — Most infrastructure already exists, Mathlib Poisson summation ready
2. **Theorem 1 (Multiplier bounds)** — Partially developed in MultiplierBound.lean, clear path forward
3. **Theorem 2 (Semigroup commutation)** — Hardest, may need Bochner integral infrastructure

## Verification

For each theorem:
1. `lake build Cylinder` — full Cylinder module builds
2. `lean_verify` on the replaced axiom → should show only standard Lean axioms + remaining axioms
3. Check downstream: `cylinderGreen_reflection_positive`, `torusGreen_uniform_bound` still build

## Files Overview

| File | Action |
|------|--------|
| `SchwartzFourier/MultiplierBound.lean` | Extend with general multiplier seminorm theorem |
| `SchwartzFourier/ResolventUniformBound.lean` | Replace axiom with proof (Theorem 1) |
| `Cylinder/GreenFunction.lean` | Replace axiom with proof (Theorem 2) |
| `Cylinder/MethodOfImages.lean` | Replace axiom with proof (Theorem 3) |
| `SchwartzNuclear/Periodization.lean` | Add L²-uniform bound for periodization |
