# Plan: n-linear Schwartz Nuclear Theorem

## Goal

Prove the axiom from OSreconstruction:
```lean
axiom schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (SchwartzMap.productTensor fs) = Phi fs
```

## What We Have

In `gaussian-field/Nuclear/`:
- `NuclearTensorProduct E₁ E₂ = RapidDecaySeq` (bilinear, over ℝ)
- `lift` + `lift_pure` + uniqueness (bilinear nuclear extension, over ℝ)
- `DyninMityaginSpace` for `SchwartzMap D ℝ` (Hermite basis)
- `NuclearTensorProduct` for 2-fold products (Cantor pairing)

## Three Gaps

### Gap 1: ℝ → ℂ scalars (~100 LOC)

**Problem:** Our `lift` works for `E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G`. The axiom needs
`ℂ`-linear maps on `ℂ`-valued Schwartz spaces.

**Approach:** The Schwartz seminorms `SchwartzMap.seminorm ℝ k l` work over ℝ
regardless of the target field. A ℂ-linear map is automatically ℝ-linear.
So:
1. Apply the ℝ-linear `lift` to the ℝ-restriction of `Phi`
2. Show the resulting extension is actually ℂ-linear (it preserves `i • x`
   because `Phi` does and pure tensors are dense)

**Alternatively:** Generalize `lift` to work over any `𝕜 : NontriviallyNormedField`
with `[NormedSpace 𝕜 E₁]` etc. This is cleaner but requires modifying
`NuclearTensorProduct.lean`.

**Recommendation:** Option 1 (restrict to ℝ, extend, verify ℂ-linearity).
Less infrastructure change.

**Difficulty:** Medium. The ℂ-linearity verification needs density of pure
tensors (already proved via `hasSum_pure`).

### Gap 2: n = 2 → general n (~200-300 LOC)

**Problem:** We have the bilinear case. Need arbitrary `n : ℕ`.

**Two approaches:**

#### Approach A: Induction (extend one factor at a time)
```
Φ : E^n → G
 ↝ For each e₁, Φ(e₁, ·) : E^{n-1} → G extends to W_{e₁} : ⊗̂^{n-1} E → G
 ↝ e₁ ↦ W_{e₁} is bilinear: E × ⊗̂^{n-1} E → G
 ↝ Extends to W : E ⊗̂ (⊗̂^{n-1} E) → G
 ↝ Use associativity ⊗̂^n E ≅ E ⊗̂ (⊗̂^{n-1} E)
```

**Pro:** Reuses bilinear `lift` directly.
**Con:** Needs iterated tensor product type `⊗̂^n E` and associativity CLE.
Lean type-level induction on `n` with dependent types is painful.

#### Approach B: Direct multi-index (recommended by Gemini)
Model the n-fold tensor product as `RapidDecaySeq` with multi-index
`Fin n → ℕ` encoded via iterated Cantor pairing. Define:
```lean
def nFoldTensorProduct (E : Type*) (n : ℕ) := RapidDecaySeq
```
with basis indexed by `(Fin n → ℕ)` and pure tensor:
```lean
def pureTensor (fs : Fin n → E) : nFoldTensorProduct E n
pureTensor fs = ∏ᵢ coeff_{mᵢ}(fᵢ) (via iterated Cantor encoding)
```

**Pro:** Direct, avoids induction on types, works with `Fin n → ℕ` natively.
**Con:** Need to reprove `lift` for n-linear maps (not just bilinear), which
requires n-fold seminorm bounds and n-fold Schauder expansion.

#### Approach C: Avoid tensor products entirely (pragmatic)
State the theorem without reference to `NuclearTensorProduct`:
```lean
theorem schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ (fun _ : Fin n => S) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d+1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs, W (productTensor fs) = Phi fs
```
Prove it directly using the multi-dimensional Hermite basis of
`SchwartzMap (Fin n → Fin (d+1) → ℝ) ℂ`. The key: any element of the
n-variable Schwartz space has a Hermite expansion, and `productTensor`
maps basis products to basis elements. The extension is:
```
W(g) = Σ_{α} ĝ(α) · Phi(h_{α₁}, ..., h_{αₙ})
```
where `ĝ(α)` are multi-index Hermite coefficients and `h_{αᵢ}` are
1-variable Hermite basis elements.

**Pro:** Most direct. No tensor product infrastructure needed.
**Con:** Need `DyninMityaginSpace (SchwartzMap (Fin n → Fin (d+1) → ℝ) ℂ)`
and the relationship between its basis and products of 1-variable bases.

**Recommendation:** Approach C. It's the most self-contained and avoids the
iterated tensor product nightmare.

### Gap 3: Connect to SchwartzMap product space (~150 LOC)

**Problem:** Need `productTensor : (Fin n → S(ℝ^{d+1})) → S(ℝ^{n(d+1)})` and
its relationship to the DM basis.

**What exists in OSreconstruction:**
- `SchwartzMap.productTensor` — defined recursively using `prependField`
- Maps `(f₁,...,fₙ) ↦ (x₁,...,xₙ) ↦ f₁(x₁)·...·fₙ(xₙ)`

**What exists in gaussian-field:**
- `schwartz_dyninMityaginSpace` — DM instance for `SchwartzMap D ℝ`
- `schwartzRapidDecayEquiv` — CLE `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`
- For multi-dim: `schwartz_dyninMityaginSpace_euclidean` using multi-index Hermite

**Key relationship to prove:**
The multi-index Hermite basis of `S(ℝ^{n(d+1)})` decomposes as products:
```
Ψ_α(x₁,...,xₙ) = ψ_{α₁}(x₁) · ... · ψ_{αₙ}(xₙ)
```
where `α = (α₁,...,αₙ)` with each `αᵢ` indexing a `(d+1)`-variable
Hermite function. This means `productTensor(ψ_{α₁},...,ψ_{αₙ}) = Ψ_α`.

**What's needed:**
1. `DyninMityaginSpace (SchwartzMap (Fin n → Fin (d+1) → ℝ) ℂ)` — instance
   for the n-variable ℂ-valued Schwartz space
2. `productTensor_basis` — pure tensor of basis = multi-index basis element
3. Summability and convergence of the multi-index Hermite expansion

**This is the hardest gap.** It requires connecting the abstract
`DyninMityaginSpace` basis with the concrete product structure of
multi-variable Schwartz functions.

## Recommended Implementation Order

### Phase 1: Infrastructure (~150 LOC, gaussian-field main)

**File:** `Nuclear/NuclearExtension.lean` (extend existing)

1. `lift` for ℂ-linear maps (or ℝ-restriction + ℂ-linearity verification)
2. General `nFold_lift` for the case where all factors are the same space

### Phase 2: Multi-variable Schwartz DM instance (~200 LOC, gaussian-field main)

**File:** `SchwartzNuclear/SchwartzMultiVariable.lean` (new)

1. `DyninMityaginSpace (SchwartzMap (Fin n → Fin (d+1) → ℝ) ℂ)` — via
   iterated tensor product or direct multi-index Hermite construction
2. `productTensor_basis` — product of Hermite basis = multi-index Hermite
3. `productTensor_continuous` — the pure tensor map is jointly continuous

### Phase 3: The nuclear theorem (~150 LOC, gaussian-field main)

**File:** `Nuclear/NuclearExtension.lean` (extend)

1. `schwartz_nuclear_extension` — the full n-linear theorem
2. Existence via multi-index Hermite expansion + continuity
3. Uniqueness via density of product tensors

### Phase 4: Bridge to OSreconstruction (~50 LOC, OSreconstruction)

1. Import from gaussian-field
2. Replace axiom with theorem
3. Verify downstream (Wightman distribution extension)

## Estimated Total: 550-700 LOC

## Hardest Parts (in order)

1. **Phase 2:** The multi-variable Schwartz DM instance and the product-basis
   relationship. This is the mathematical core.
2. **Gap 1 (ℂ scalars):** Not conceptually hard but Lean's scalar tower
   (`ℝ ⊂ ℂ`) creates typeclass headaches.
3. **Phase 3:** Once Phase 2 is done, the extension theorem follows the
   same pattern as the bilinear case.

## Dependencies

- gaussian-field: `Nuclear/NuclearTensorProduct.lean`, `Nuclear/NuclearExtension.lean`,
  `SchwartzNuclear/HermiteNuclear.lean`, `SchwartzNuclear/SchwartzTensorProduct.lean`
- Mathlib: `Analysis.Distribution.SchwartzSpace`, `Analysis.InnerProductSpace.Basic`,
  `Analysis.SpecialFunctions.Hermite`
- OSreconstruction: `Wightman/SchwartzTensorProduct.lean` (for `productTensor`)

## Alternative: Axiomatize Phase 2 only

If Phase 2 is too hard, axiomatize just the product-basis relationship:
```lean
axiom productTensor_basis_eq (d n : ℕ) (α : Fin n → ℕ) :
    SchwartzMap.productTensor (fun i => DyninMityaginSpace.basis (α i)) =
    DyninMityaginSpace.basis (cantorEncode α)
```
Then Phase 3 follows mechanically. This isolates the hard analysis
(multi-variable Hermite products = multi-index Hermite) as a single axiom
that can be proved later.
