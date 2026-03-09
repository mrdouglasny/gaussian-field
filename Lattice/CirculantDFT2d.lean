/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 2D Circulant DFT Spectral Expansion

Extends the 1D DFT spectral expansion to prove `lattice_covariance_pure_eq_2d_spectral`:
the lattice covariance for pure tensors equals the 2D DFT spectral sum.

## Main results

- `dft_1d_eigenvalue_pointwise` — 1D eigenvalue identity at the ZMod level
- `massOperator_product_eigenvector` — product of 1D DFT eigenvectors is a 2D eigenvector
- `dft_parseval_1d` — 1D DFT Parseval identity
- `dft_parseval_2d` — 2D DFT Parseval identity (product of 1D Parsevals)
- `abstract_spectral_eq_dft_spectral_2d` — abstract spectral expansion = DFT spectral expansion

## References

- Davis, *Circulant Matrices*, Ch. 5
-/

import Lattice.CirculantDFT
import Lattice.SpectralCovariance
import Lattice.Covariance

noncomputable section

namespace GaussianField

open Matrix Finset

variable (N : ℕ) [NeZero N]

/-! ## 1D eigenvalue identity (pointwise, on ZMod N) -/

/-- The 1D DFT eigenvalue identity at a single point `z ∈ ZMod N`:

`-(a⁻¹² · (φ_m(z+1) + φ_m(z-1) - 2·φ_m(z))) = λ_m · φ_m(z)`

This extracts the pointwise content of `negLaplacian1d_dft_eigenvector`,
bridging from the matrix/CLM level to a raw ZMod N computation. -/
theorem dft_1d_eigenvalue_pointwise (a : ℝ) (ha : a ≠ 0)
    (m : ℕ) (hm : m < N) (z : ZMod N) :
    -(a⁻¹ ^ 2 * (latticeFourierBasisFun N m (z + 1) +
                  latticeFourierBasisFun N m (z - 1) -
                  2 * latticeFourierBasisFun N m z)) =
    latticeEigenvalue1d N a m * latticeFourierBasisFun N m z := by
  set y : FinLatticeSites 1 N := fun _ => z
  have hev := congr_fun (negLaplacian1d_dft_eigenvector N a ha m hm) y
  simp only [Pi.smul_apply, smul_eq_mul] at hev
  rw [show (negLaplacianMatrix 1 N a).mulVec
      (fun x : FinLatticeSites 1 N => latticeFourierBasisFun N m (x 0)) y =
      (massOperator 1 N a 0
        (fun x : FinLatticeSites 1 N => latticeFourierBasisFun N m (x 0))) y from by
    simp only [negLaplacianMatrix]
    rw [← massOperator_eq_matrix_mulVec]] at hev
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul, sq, mul_zero, zero_mul, add_zero] at hev
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun] at hev
  simp only [Fin.sum_univ_one] at hev
  simp only [show y 0 = z from rfl, ite_true] at hev
  linarith

/-! ## 2D product eigenvector -/

/-- The 2D mass operator applied to a product of 1D DFT eigenvectors yields
`(λ_{m₁} + λ_{m₂} + mass²) · w`, proving w is an eigenvector. -/
theorem massOperator_product_eigenvector (a mass : ℝ) (ha : a ≠ 0)
    (m₁ m₂ : ℕ) (hm₁ : m₁ < N) (hm₂ : m₂ < N)
    (x : FinLatticeSites 2 N) :
    (massOperator 2 N a mass
      (fun y : FinLatticeSites 2 N =>
        latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1))) x =
    (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
      (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun]
  rw [show Finset.univ (α := Fin 2) = {0, 1} from by ext i; fin_cases i <;> simp]
  rw [Finset.sum_pair (by omega : (0 : Fin 2) ≠ 1)]
  have h10 : ¬((1 : Fin 2) = 0) := by omega
  have h01 : ¬((0 : Fin 2) = 1) := by omega
  simp only [Fin.isValue, ↓reduceIte, if_neg h10, if_neg h01]
  have h1d₁ := dft_1d_eigenvalue_pointwise N a ha m₁ hm₁ (x 0)
  have h1d₂ := dft_1d_eigenvalue_pointwise N a ha m₂ hm₂ (x 1)
  linear_combination
    latticeFourierBasisFun N m₂ (x 1) * h1d₁ +
    latticeFourierBasisFun N m₁ (x 0) * h1d₂

/-! ## 1D DFT Parseval identity -/

/-- The 1D DFT Parseval identity: the inner product equals the spectral sum
weighted by inverse norms squared. Follows from `dft_expansion`. -/
theorem dft_parseval_1d (f g : ZMod N → ℝ) :
    ∑ z : ZMod N, f z * g z =
    ∑ m : Fin N,
      (∑ z : ZMod N, f z * latticeFourierBasisFun N m z) *
      (∑ z : ZMod N, g z * latticeFourierBasisFun N m z) /
      latticeFourierNormSq N m := by
  -- Substitute the DFT expansion of f into the LHS
  have hexp := dft_expansion N f
  conv_lhs => rw [hexp]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- LHS = ∑_z (∑_m c_m/ns_m * φ_m(z)) * g(z)
  -- Distribute g(z) into the inner sum (LHS only)
  conv_lhs => arg 2; ext z; rw [Finset.sum_mul]
  -- LHS = ∑_z ∑_m (c_m/ns_m * φ_m(z)) * g(z)
  rw [Finset.sum_comm]
  -- LHS = ∑_m ∑_z (c_m/ns_m * φ_m(z)) * g(z)
  refine Finset.sum_congr rfl fun m _ => ?_
  -- Each term: (c/ns * φ(z)) * g(z) → c/ns * (g(z) * φ(z)) by ring
  conv_lhs => arg 2; ext z; rw [show
    ((∑ w, f w * latticeFourierBasisFun N (↑m) w) / latticeFourierNormSq N ↑m *
      latticeFourierBasisFun N (↑m) z) * g z =
    (∑ w, f w * latticeFourierBasisFun N (↑m) w) / latticeFourierNormSq N ↑m *
      (g z * latticeFourierBasisFun N (↑m) z) from by ring]
  -- Factor out c/ns
  rw [← Finset.mul_sum]
  -- c/ns * d = c * d / ns
  ring

/-! ## 2D DFT Parseval identity -/

/-- Factor a sum over `FinLatticeSites 2 N` as a double sum over `ZMod N`. -/
lemma sum_factor (F : FinLatticeSites 2 N → ℝ) :
    ∑ x : FinLatticeSites 2 N, F x = ∑ a : ZMod N, ∑ b : ZMod N, F ![a, b] := by
  rw [← Fintype.sum_prod_type' (fun a b => F ![a, b])]
  exact Fintype.sum_equiv (finTwoArrowEquiv (ZMod N)) _ _ (fun x => by
    congr 1; ext i; fin_cases i <;> simp [finTwoArrowEquiv, piFinTwoEquiv])

/-- The 2D DFT Parseval identity: the inner product on `FinLatticeSites 2 N`
equals the spectral sum over the 2D product DFT basis. -/
theorem dft_parseval_2d (f g : FinLatticeSites 2 N → ℝ) :
    ∑ x : FinLatticeSites 2 N, f x * g x =
    ∑ m₁ : Fin N, ∑ m₂ : Fin N,
      (∑ x : FinLatticeSites 2 N,
        f x * (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1))) *
      (∑ x : FinLatticeSites 2 N,
        g x * (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1))) /
      (latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
  -- Helper: DFT coefficient factors as iterated 1D operations
  have coeff_factor : ∀ (h : FinLatticeSites 2 N → ℝ) (m₁ m₂ : Fin N),
      ∑ x : FinLatticeSites 2 N,
        h x * (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) =
      ∑ a : ZMod N, (∑ b : ZMod N, h ![a, b] * latticeFourierBasisFun N ↑m₂ b) *
        latticeFourierBasisFun N ↑m₁ a := by
    intro h m₁ m₂
    rw [sum_factor]
    congr 1; ext a
    rw [Finset.sum_mul]
    congr 1; ext b
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  -- Step 1: Factor LHS sum
  rw [sum_factor]
  -- Step 2: Apply 1D Parseval in b for each a
  simp_rw [dft_parseval_1d N (fun b => f ![_, b]) (fun b => g ![_, b])]
  -- Step 3: Swap ∑ a, ∑ m₂ → ∑ m₂, ∑ a
  rw [Finset.sum_comm]
  -- Step 4: For each m₂, factor out /ns(m₂) and apply 1D Parseval in a
  conv_lhs => arg 2; ext m₂; rw [← Finset.sum_div,
    dft_parseval_1d N
      (fun a => ∑ b, f ![a, b] * latticeFourierBasisFun N ↑m₂ b)
      (fun a => ∑ b, g ![a, b] * latticeFourierBasisFun N ↑m₂ b),
    Finset.sum_div]
  -- Step 5: Swap ∑ m₂, ∑ m₁ → ∑ m₁, ∑ m₂ to match theorem statement
  rw [Finset.sum_comm]
  -- Step 6: Match each summand
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  -- Replace factored coefficients with full FinLatticeSites sums
  rw [← coeff_factor f m₁ m₂, ← coeff_factor g m₁ m₂]
  -- Combine /ns(m₁)/ns(m₂) into /(ns(m₁)*ns(m₂))
  ring

/-! ## Mass operator surjectivity -/

/-- The mass operator on `FinLatticeSites 2 N` is surjective, since it is
positive definite on a finite-dimensional space. -/
theorem massOperator_surjective_2d (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Function.Surjective (massOperator 2 N a mass) := by
  -- Positive definite ⟹ injective ⟹ surjective (finite dim)
  have hinj : Function.Injective (massOperator 2 N a mass) := by
    intro f g hfg
    by_contra hne
    have hne' : f - g ≠ 0 := sub_ne_zero.mpr hne
    have hpos := massOperator_pos_def 2 N a mass ha hmass (f - g) hne'
    have hzero : ∑ x, (f - g) x * (massOperator 2 N a mass (f - g)) x = 0 := by
      have : massOperator 2 N a mass (f - g) = 0 := by
        ext x; simp [map_sub, hfg, sub_self]
      simp [this]
    linarith
  exact (massOperator 2 N a mass).toLinearMap.surjective_of_injective hinj

/-! ## DFT eigencoefficient for mass operator -/

/-- The DFT eigencoefficient identity: the inner product of a 2D DFT product
eigenvector with Q·h equals the eigenvalue times the inner product with h.
Follows from Q being self-adjoint and the product eigenvector property. -/
theorem dft_eigencoeff_massOperator_2d (a mass : ℝ) (ha : a ≠ 0)
    (m₁ m₂ : ℕ) (hm₁ : m₁ < N) (hm₂ : m₂ < N)
    (h : FinLatticeSites 2 N → ℝ) :
    (∑ x : FinLatticeSites 2 N,
      (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) *
      (massOperator 2 N a mass h) x) =
    (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
      (∑ x : FinLatticeSites 2 N,
        (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) * h x) := by
  -- Use Q self-adjoint: ⟨ψ, Qh⟩ = ⟨Qψ, h⟩
  rw [massOperator_selfAdjoint 2 N a mass
    (fun y => latticeFourierBasisFun N m₁ (y 0) * latticeFourierBasisFun N m₂ (y 1)) h]
  -- Expand RHS: ev * ∑_x ψ(x) * h(x) = ∑_x ev * (ψ(x) * h(x))
  rw [Finset.mul_sum]
  -- For each x: (Qψ)(x) * h(x) = ev * (ψ(x) * h(x))
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [massOperator_product_eigenvector N a mass ha m₁ m₂ hm₁ hm₂ x]
  ring

/-! ## Main spectral identity -/

/-- The abstract spectral covariance equals the 2D DFT spectral sum.
Both represent `⟨f, Q⁻¹g⟩` — the abstract form using Mathlib's eigenbasis,
the DFT form using the product DFT eigenbasis. The proof shows both give
`∑_x f(x)·h(x)` when `g = Q·h`, then uses surjectivity of Q. -/
theorem abstract_spectral_eq_dft_spectral_2d (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeSites 2 N → ℝ) :
    covariance (latticeCovariance 2 N a mass ha hmass) f g =
    ∑ m₁ : Fin N, ∑ m₂ : Fin N,
      (∑ x, f x * (latticeFourierBasisFun N m₁ (x 0) *
        latticeFourierBasisFun N m₂ (x 1))) *
      (∑ x, g x * (latticeFourierBasisFun N m₁ (x 0) *
        latticeFourierBasisFun N m₂ (x 1))) /
      ((latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) *
       latticeFourierNormSq N m₁ * latticeFourierNormSq N m₂) := by
  -- Suffices to show equality for g in the range of Q (since Q is surjective)
  obtain ⟨h, rfl⟩ := massOperator_surjective_2d N a mass ha hmass g
  have ha' : a ≠ 0 := ne_of_gt ha
  -- Both sides equal ∑_x f(x) * h(x)
  trans (∑ x : FinLatticeSites 2 N, f x * h x)
  · -- LHS = ∑_x f(x) * h(x) via abstract spectral cancellation
    rw [lattice_covariance_eq_spectral]
    -- Replace ⟨e_k, Qh⟩ = λ_k * ⟨e_k, h⟩
    simp_rw [massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff (d := 2) (N := N) a mass h]
    -- Cancel λ_k⁻¹ * λ_k, then use abstract Parseval
    refine Eq.trans ?_
      (massEigenbasis_sum_mul_sum_eq_site_inner (d := 2) (N := N) a mass f h)
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : massEigenvalues 2 N a mass k ≠ 0 :=
      ne_of_gt (massOperatorMatrix_eigenvalues_pos 2 N a mass ha hmass k)
    field_simp
  · -- ∑_x f(x) * h(x) = RHS via DFT eigencoeff cancellation
    rw [dft_parseval_2d]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    -- Replace ⟨Qh, ψ_m⟩ = μ_m * ⟨h, ψ_m⟩
    have heig := dft_eigencoeff_massOperator_2d N a mass ha' m₁ m₂ m₁.isLt m₂.isLt h
    -- Reorder: ⟨ψ, Qh⟩ → ⟨Qh, ψ⟩
    have heig' : ∑ x : FinLatticeSites 2 N,
        (massOperator 2 N a mass h) x *
        (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) =
      (latticeEigenvalue1d N a ↑m₁ + latticeEigenvalue1d N a ↑m₂ + mass ^ 2) *
        (∑ x, h x * (latticeFourierBasisFun N m₁ (x 0) *
          latticeFourierBasisFun N m₂ (x 1))) := by
      rw [show ∑ x, (massOperator 2 N a mass h) x *
          (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) =
        ∑ x, (latticeFourierBasisFun N m₁ (x 0) * latticeFourierBasisFun N m₂ (x 1)) *
          (massOperator 2 N a mass h) x from
        Finset.sum_congr rfl fun x _ => mul_comm _ _]
      rw [heig]
      congr 1
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [heig']
    -- Cancel μ_m in numerator and denominator
    have hμ : 0 < latticeEigenvalue1d N a ↑m₁ + latticeEigenvalue1d N a ↑m₂ + mass ^ 2 := by
      have := latticeEigenvalue1d_nonneg N a m₁
      have := latticeEigenvalue1d_nonneg N a m₂
      positivity
    field_simp

end GaussianField

end
