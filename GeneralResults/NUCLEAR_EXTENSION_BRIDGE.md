# Bridge: gaussian-field → OSreconstruction schwartz_nuclear_extension

## How to replace the axiom in OSreconstruction

The axiom `schwartz_nuclear_extension` in `OSReconstruction/Wightman/WightmanAxioms.lean`
can be proved from the infrastructure on the `extension` branch of gaussian-field.

### Step 1: Update OSreconstruction's GaussianField dependency

In `lakefile.toml`, update the GaussianField rev to point to the `extension` branch:
```toml
[[require]]
name = "GaussianField"
git = "https://github.com/mrdouglasny/gaussian-field.git"
rev = "<extension branch HEAD commit>"
```

Also update lean-toolchain to match gaussian-field (v4.29.0-rc6).

### Step 2: Create the bridge theorem

In OSreconstruction, create a file importing both gaussian-field infrastructure
and the existing `SchwartzMap.productTensor`:

```lean
import GeneralResults.SchwartzProducts
import SchwartzNuclear.NuclearExtension
import OSReconstruction.Wightman.SchwartzTensorProduct

theorem schwartz_nuclear_extension (d n : ℕ)
    (Phi : ContinuousMultilinearMap ℂ
      (fun _ : Fin n => SchwartzMap (Fin (d + 1) → ℝ) ℂ) ℂ) :
    ∃! (W : SchwartzMap (Fin n → Fin (d + 1) → ℝ) ℂ →L[ℂ] ℂ),
      ∀ fs : Fin n → SchwartzMap (Fin (d + 1) → ℝ) ℂ,
        W (SchwartzMap.productTensor fs) = Phi fs := by
  -- Proof sketch:
  -- 1. UNIQUENESS: If W₁, W₂ agree on productTensor, then W := W₁ - W₂
  --    vanishes on all productTensor. Since W is ℂ-linear, W(f) = W(Re f) + i·W(Im f).
  --    Restrict to real-valued: w := Re(W)|_{S(prod,ℝ)} and Im(W)|_{S(prod,ℝ)} are ℝ-linear CLFs.
  --    Each vanishes on real product Hermite functions (since productTensor of real = real product).
  --    By productHermite_schwartz_dense, w = 0. So W = 0, hence W₁ = W₂.
  --
  -- 2. EXISTENCE: Restrict Phi to real Schwartz → get Phi_ℝ : S(D,ℝ)^n → ℂ.
  --    Decompose: Re(Phi_ℝ), Im(Phi_ℝ) are ℝ-multilinear to ℝ.
  --    By multilinear_on_basis_bound + exists_unique_clm_of_polyBounded:
  --    construct w_re, w_im : S(prod,ℝ) →L[ℝ] ℝ extending Re/Im of Phi_ℝ.
  --    Combine: w := w_re + i·w_im : S(prod,ℝ) →L[ℝ] ℂ.
  --    Complexify: W(f) := w(Re f) + i·w(Im f) : S(prod,ℂ) →L[ℂ] ℂ.
  --
  -- 3. AGREEMENT: W(productTensor(f₁,...,fₙ)) = Phi(f₁,...,fₙ) for ℂ-valued fᵢ.
  --    Decompose each fᵢ = Re(fᵢ) + i·Im(fᵢ). By ℂ-multilinearity of both sides,
  --    expand into 2^n terms. Each term involves real-valued product tensors,
  --    where agreement follows from the ℝ-valued construction.
  sorry
```

### Step 3: Fill the complexification

The complexification (ℝ → ℂ extension) is ~100 lines of algebraic manipulation:
- `W(f) = w(Re f) + i·w(Im f)` is ℂ-linear: check W(i·f) = i·W(f)
- Continuity: Re, Im are continuous ℝ-linear on S(prod,ℂ), and w is continuous
- Agreement on product tensors: expand via multilinearity of Phi and productTensor

### Available gaussian-field infrastructure (extension branch)

| Theorem | File | What it gives |
|---|---|---|
| `exists_unique_clm_of_polyBounded` | NuclearExtension.lean | ∃! CLM from poly-bounded basis values |
| `multilinear_on_basis_bound` | NuclearExtension.lean | |Phi(ψ_k)| ≤ C·∏(1+kᵢ)^s |
| `productHermite_schwartz_dense` | SchwartzProducts.lean | CLF vanishing on product Hermite = 0 |
| `schwartzProductTensor_schwartz` | SchwartzProducts.lean | Product of Schwartz is Schwartz |
| `clm_eq_of_basis_eq` | NuclearExtension.lean | CLMs determined by basis values |
| `abs_tsum_le_of_pointwise_le` | TsumBound.lean | Tsum bound helper |

All proved with 0 sorry, 0 axioms (only standard Lean axioms).
