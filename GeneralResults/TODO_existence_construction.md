# TODO: Fill existence sorry in schwartz_nuclear_extension

**File**: `GeneralResults/NuclearExtensionComplex.lean`, line 515
**Goal**: `∃ W : S(∏D, ℂ) →L[ℂ] ℂ, ∀ fs, W(complexProductTensor fs) = Phi fs`

## What's proved

- **Uniqueness**: fully proved (0 sorry) — lines 516-619
- **All ℝ-valued infrastructure**: 0 sorry across 3 files
- **complexProductTensor**: defined, `_apply` proved, `_update_add/_smul` proved
- **IsScalarTower ℝ ℂ (SchwartzMap D ℂ)**: instance proved

## Verified in lean_run_code (not yet written to file)

### 1. complexifyCLM compiles
```lean
def complexifyCLM {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w_re w_im : E →L[ℝ] ℝ) : E →L[ℝ] ℂ where
  toFun f := ⟨w_re f, w_im f⟩
  map_add' f g := by ext <;> simp [map_add]
  map_smul' r f := by ext <;> simp [map_smul, Complex.ofReal_re, Complex.ofReal_im]
  cont := by exact continuous_induced_rng.mpr ⟨w_re.cont, w_im.cont⟩
```

### 2. Phi.restrictScalars ℝ works
With the IsScalarTower instance, `Phi.restrictScalars ℝ` gives an ℝ-multilinear map.

### 3. Phi_re and Phi_im can be extracted
```lean
-- Compose Phi with iotaSchwartz to evaluate on real inputs, then take Re/Im
Phi_real gs := Phi (fun i => iotaSchwartz D (gs i))  -- ℂ-valued
Phi_re gs := Complex.re (Phi_real gs)                 -- ℝ-valued
Phi_im gs := Complex.im (Phi_real gs)                 -- ℝ-valued
```
These are continuous ℝ-multilinear maps `S(D, ℝ)^n → ℝ`.

## What remains to write (~200 lines)

### A. Multi-index growth bound (~80 lines)
Show `productBasisIndices m i` (the per-factor DM basis index for flat index m)
grows polynomially in m. This is:
```
productBasisIndices m i = multiIndexEquiv (blockMultiIndex (multiIndexEquiv.symm m) i)
```
Need: `∃ C > 0, ∃ q, ∀ m i, productBasisIndices m i ≤ C * (1+m)^q`

This follows from polynomial bounds on `multiIndexEquiv` (Cantor pairing grows
polynomially) composed with `blockMultiIndex` (restriction to a block).

### B. Construct w_re, w_im (~30 lines)
Apply `multilinear_on_basis_bound` to `Phi_re` and `Phi_im` to get polynomial growth.
Apply `multilinear_on_basis_polyBounded` with the encoding from (A).
Apply `exists_unique_clm_of_polyBounded` to construct:
```
w_re : S(∏D, ℝ) →L[ℝ] ℝ  with w_re(∏ ψ_{kᵢ}) = Phi_re(ψ_{k₁},...,ψ_{kₙ})
w_im : S(∏D, ℝ) →L[ℝ] ℝ  with w_im(∏ ψ_{kᵢ}) = Phi_im(ψ_{k₁},...,ψ_{kₙ})
```

### C. Build W = complexifyCLM w_re w_im composed with Re/Im extraction (~20 lines)
```
W(f) = complexifyCLM w_re w_im (Re f) + i * complexifyCLM w_re w_im (Im f)
```
Or more precisely, using `schwartz_complex_decomp`:
```
W(f) = (w_re(Re f) - w_im(Im f)) + i * (w_im(Re f) + w_re(Im f))
```
Show this is ℂ-linear: check `W(i·f) = i·W(f)` and `W(c·f) = c·W(f)`.

### D. Agreement proof (~70 lines)
Show `W(complexProductTensor fs) = Phi fs` for ℂ-valued fs.

Decompose each `fs i = ι(Re(fs i)) + i·ι(Im(fs i))`.
By ℂ-multilinearity of both `W ∘ complexProductTensor` and `Phi`:
- Both sides expand into `2^n` terms (one for each Re/Im choice per factor)
- Each term involves products of real-valued functions
- For real products: `W(ι(∏ gs i (x i))) = w_re(∏ gs i (x i)) + i·w_im(∏ gs i (x i))`
  = `Phi_re(gs) + i·Phi_im(gs) = Phi(ι(g₁),...,ι(gₙ))`
- The 2^n expansion of both sides matches term by term

The 2^n expansion can be done by induction on n, peeling one factor at a time
and using ℂ-linearity in that slot.

## Key available lemmas

| Lemma | File | What |
|---|---|---|
| `exists_unique_clm_of_polyBounded` | NuclearExtension | ∃! CLM from poly-bounded basis values |
| `multilinear_on_basis_bound` | NuclearExtension | |Phi(ψ_k)| ≤ C·∏(1+kᵢ)^s |
| `multilinear_on_basis_polyBounded` | NuclearExtension | poly bound for encoded basis values |
| `productHermite_schwartz_dense` | SchwartzProducts | density of product Hermite |
| `schwartzProductTensor_schwartz` | SchwartzProducts | product of Schwartz is Schwartz |
| `productEquiv_symm_basisVec_isProductHermite` | SchwartzProducts | basis factors as products |
| `complexProductTensor_ofReal` | NuclearExtensionComplex | product of real-embedded = embed of product |
| `schwartz_complex_decomp` | NuclearExtensionComplex | f = ι(Re f) + i·ι(Im f) |
| `complexifyCLM` | (to define) | ℝ-linear pair → ℂ-valued CLM |
