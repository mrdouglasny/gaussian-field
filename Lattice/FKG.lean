/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FKG Inequality for Lattice Gaussian Measures

Proves and states the FKG (Fortuin-Kasteleyn-Ginibre) inequality for the lattice
Gaussian measure and for measures with single-site perturbations.

## Main definitions

- `FKGLatticeCondition` — the FKG lattice condition (log-supermodularity)
- `IsSubmodular` — submodularity for functions on `ι → ℝ`
- `IsSingleSite` — perturbation V decomposes as a sum of single-site functions
- `IsFieldMonotone` — monotonicity for functions on Configuration space
- `gaussianDensity` — unnormalized Gaussian density exp(-½⟨φ,Qφ⟩)

## Main theorems (proved)

- `chebyshev_integral_inequality` — 1D FKG (base case)
- `algebraic_four_functions` — key algebraic lemma for AD
- `ahlswede_daykin_one_dim` — 1D continuous Ahlswede-Daykin theorem
- `ad_marginal_preservation_ae` — AD condition preserved by Fubini marginalization
- `ahlswede_daykin` — n-dimensional Ahlswede-Daykin by Fubini induction
- `fkg_from_lattice_condition_nonneg` — FKG for nonneg monotone functions (via AD)
- `fkg_from_lattice_condition` — general FKG via truncation + shift invariance
- `fkg_lattice_condition_mul` — product preserves FKG lattice condition
- `fkg_lattice_condition_single_site` — single-site exp(-V) satisfies FKG
- `fkg_lattice_condition_of_submodular` — exp(-V) satisfies FKG if V submodular
- `sup_inf_mul_add_le` — max-min product inequality (algebra)
- `quadraticForm_submodular_of_nonpos_offDiag` — quadratic forms with
  non-positive off-diagonal are submodular
- `gaussianDensity_fkg_lattice_condition` — Gaussian density satisfies FKG

## Axioms (8 textbook results for later proof)

- `fubini_pi_decomp` — Fubini decomposition of ∫ over (ι → ℝ)
- `integrable_marginal` — marginal of nonneg integrable function is integrable
- `integrable_fiber_ae` — fiber integrability for a.e. remaining coordinates
- `integral_empty_pi` — integral over empty pi type = point evaluation
- `fkg_truncation_dct` — DCT for truncation max(F, -n) * ρ → F * ρ
- `fkg_truncation_dct_prod` — DCT for product truncation
- `integrable_truncation_mul` — integrability of max(F, -n) * ρ
- `integrable_truncation_prod_mul` — integrability of max(F,-n) * max(G,-n) * ρ

## Sorrys (7 routine steps)

- `ad_marginal_preservation_ae` — a.e. fiber integrability argument (uses
  `integrable_fiber_ae` + 1D AD on fibers)
- `ahlswede_daykin` base case — integral over singleton space
- `fkg_from_lattice_condition` — 3 integrability goals, shift invariance
  algebra, and limit passage via DCT

## Proved (formerly axioms)

- `latticeGaussianMeasure_density_integral` — density bridge: proved in
  `GaussianField.Density` via characteristic function matching
- `integrable_mul_gaussianDensity` — integrability transfer: proved in
  `GaussianField.Density` via density bridge

## Derived theorems

- `gaussian_fkg_lattice_condition` — FKG for Gaussian measure
- `fkg_perturbed` — FKG for single-site perturbations

## Proof architecture (Ahlswede-Daykin approach)

```
algebraic_four_functions → ahlswede_daykin_one_dim → ahlswede_daykin (n-dim)
                                                            ↓
  fkg_from_lattice_condition_nonneg ← AD + FKG lattice condition + monotonicity
                                                            ↓
  fkg_from_lattice_condition ← truncation + DCT + nonneg version
                                                            ↓
massOperator_offDiag_nonpos → quadraticForm_submodular → gaussianDensity_fkg
                                                              ↓
  fkg_from_lattice_condition + density bridge → gaussian_fkg_lattice_condition
                                                              ↓
  + fkg_lattice_condition_single_site + fkg_lattice_condition_mul → fkg_perturbed
```

## References

- Ahlswede, Daykin (1978), "An inequality for the weights of two families
  of sets"
- Fortuin, Kasteleyn, Ginibre (1971), "Correlation inequalities on some
  partially ordered sets"
- Holley (1974), "Remarks on the FKG inequalities"
- Glimm-Jaffe, "Quantum Physics", §19 (Correlation inequalities)
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", §IV
-/

import Lattice.Covariance
import GaussianField.Density
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace GaussianField

open MeasureTheory

/-! ## 1D Chebyshev integral inequality

The base case of FKG: for any probability measure on ℝ, monotone functions
are positively correlated. This holds without any log-concavity assumption.

Proof: `(f(x) - f(y))(g(x) - g(y)) ≥ 0` for monotone f, g; integrate over
the product measure `μ ⊗ μ` and expand. -/

/-- **Chebyshev's integral inequality.**
For any probability measure μ on ℝ, if f and g are both monotone, then
`E[f·g] ≥ E[f]·E[g]`. This is the 1D base case of the FKG inequality
and requires no log-concavity assumption. -/
theorem chebyshev_integral_inequality (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : Monotone f) (hg : Monotone g)
    (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (f * g) μ)
    (hexpand : Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2))
      (μ.prod μ)) :
    (∫ x, f x * g x ∂μ) ≥ (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  -- Key: (f(x) - f(y))(g(x) - g(y)) ≥ 0 for monotone f, g
  have hnn : ∀ x y : ℝ, 0 ≤ (f x - f y) * (g x - g y) := by
    intro x y
    by_cases h : x ≤ y
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf h)) (sub_nonpos.mpr (hg h))
    · push_neg at h
      exact mul_nonneg (sub_nonneg.mpr (hf (le_of_lt h))) (sub_nonneg.mpr (hg (le_of_lt h)))
  -- ∫∫ (f(x) - f(y))(g(x) - g(y)) d(μ⊗μ) ≥ 0
  have hint_nn : 0 ≤ ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) :=
    integral_nonneg (fun p => hnn p.1 p.2)
  -- The expansion: ∫∫ (f x - f y)(g x - g y) d(μ⊗μ) = 2·∫fg dμ - 2·(∫f)(∫g)
  -- This uses Fubini + integral_prod_mul for cross terms and
  -- marginalization for diagonal terms (probability measure has total mass 1).
  have hexpand_eq : ∫ p, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) =
      2 * (∫ x, f x * g x ∂μ) - 2 * ((∫ x, f x ∂μ) * (∫ x, g x ∂μ)) := by
    -- Strategy: use Fubini, compute inner integral, compute outer integral.
    -- Fubini
    rw [integral_prod (f := fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2)) hexpand]
    -- Inner integral for fixed x
    have inner_eq : ∀ x, ∫ y, (f x - f y) * (g x - g y) ∂μ =
        f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x +
        ∫ y, f y * g y ∂μ := by
      intro x
      have h1 : Integrable (fun _ : ℝ => f x * g x) μ := integrable_const _
      have h2 : Integrable (fun y => f x * g y) μ := hgi.const_mul _
      have h3 : Integrable (fun y => f y * g x) μ := hfi.mul_const _
      have split1 : ∫ y, (f x - f y) * (g x - g y) ∂μ =
          (∫ y, (f x * g x - f x * g y - f y * g x) ∂μ) + ∫ y, f y * g y ∂μ := by
        rw [show (∫ y, (f x - f y) * (g x - g y) ∂μ) =
            ∫ y, ((f x * g x - f x * g y - f y * g x) + f y * g y) ∂μ from
          integral_congr_ae (by filter_upwards with y; ring)]
        exact integral_add (h1.sub h2 |>.sub h3) hfgi
      have split2 : ∫ y, (f x * g x - f x * g y - f y * g x) ∂μ =
          (∫ y, (f x * g x - f x * g y) ∂μ) - ∫ y, f y * g x ∂μ := by
        rw [show (∫ y, (f x * g x - f x * g y - f y * g x) ∂μ) =
            ∫ y, ((f x * g x - f x * g y) - f y * g x) ∂μ from
          integral_congr_ae (by filter_upwards with y; ring)]
        exact integral_sub (h1.sub h2) h3
      have split3 : ∫ y, (f x * g x - f x * g y) ∂μ =
          (∫ _, f x * g x ∂μ) - ∫ y, f x * g y ∂μ := integral_sub h1 h2
      rw [split1, split2, split3]
      simp only [integral_const, integral_const_mul, integral_mul_const, probReal_univ,
        one_smul]
    simp_rw [inner_eq]
    -- Outer integral
    have osplit1 : ∫ x, (f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x +
        ∫ y, f y * g y ∂μ) ∂μ =
        (∫ x, (f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x) ∂μ) +
        ∫ _, (∫ y, f y * g y ∂μ) ∂μ := by
      rw [show (∫ x, (f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x +
          ∫ y, f y * g y ∂μ) ∂μ) =
          ∫ x, ((f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x) +
          ∫ y, f y * g y ∂μ) ∂μ from
        integral_congr_ae (by filter_upwards with x; ring)]
      exact integral_add
        (hfgi.sub (hfi.mul_const _) |>.sub (hgi.const_mul _)) (integrable_const _)
    have osplit2 : ∫ x, (f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x) ∂μ =
        (∫ x, (f x * g x - f x * (∫ y, g y ∂μ)) ∂μ) -
        ∫ x, (∫ y, f y ∂μ) * g x ∂μ := by
      rw [show (∫ x, (f x * g x - f x * (∫ y, g y ∂μ) - (∫ y, f y ∂μ) * g x) ∂μ) =
          ∫ x, ((f x * g x - f x * (∫ y, g y ∂μ)) - (∫ y, f y ∂μ) * g x) ∂μ from
        integral_congr_ae (by filter_upwards with x; ring)]
      exact integral_sub (hfgi.sub (hfi.mul_const _)) (hgi.const_mul _)
    have osplit3 : ∫ x, (f x * g x - f x * (∫ y, g y ∂μ)) ∂μ =
        (∫ x, f x * g x ∂μ) - ∫ x, f x * (∫ y, g y ∂μ) ∂μ :=
      integral_sub hfgi (hfi.mul_const _)
    rw [osplit1, osplit2, osplit3]
    simp only [integral_const, integral_const_mul, integral_mul_const, probReal_univ,
      one_smul]
    ring
  -- Combine: 0 ≤ 2·(∫fg dμ - (∫f)(∫g))
  linarith

/-! ## FKG lattice condition

The FKG lattice condition is the key structural property of a density that
enables the FKG correlation inequality. For a function ρ : (ι → ℝ) → ℝ,
it states that ρ is "supermodular" with respect to the componentwise lattice
structure: `ρ(x ⊔ y) · ρ(x ⊓ y) ≥ ρ(x) · ρ(y)`. -/

variable {ι : Type*} [Fintype ι]

/-- The **FKG lattice condition** for a function ρ on a product of linearly
ordered sets. States that ρ is log-supermodular:
`ρ(x ⊔ y) · ρ(x ⊓ y) ≥ ρ(x) · ρ(y)` where ⊔ and ⊓ are componentwise
max and min on `ι → ℝ`. -/
def FKGLatticeCondition (ρ : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y : ι → ℝ, ρ (x ⊔ y) * ρ (x ⊓ y) ≥ ρ x * ρ y

/-- The product of two FKG-lattice functions is FKG-lattice. -/
theorem fkg_lattice_condition_mul {ι : Type*} {ρ₁ ρ₂ : (ι → ℝ) → ℝ}
    (h₁ : FKGLatticeCondition ρ₁) (h₂ : FKGLatticeCondition ρ₂)
    (hnn₁ : ∀ x, 0 ≤ ρ₁ x) (hnn₂ : ∀ x, 0 ≤ ρ₂ x) :
    FKGLatticeCondition (ρ₁ * ρ₂) := by
  intro x y
  simp only [Pi.mul_apply]
  -- ρ₁(x⊔y)·ρ₂(x⊔y)·ρ₁(x⊓y)·ρ₂(x⊓y) ≥ ρ₁(x)·ρ₂(x)·ρ₁(y)·ρ₂(y)
  -- follows from: ρ₁(x⊔y)·ρ₁(x⊓y) ≥ ρ₁(x)·ρ₁(y)
  --          and: ρ₂(x⊔y)·ρ₂(x⊓y) ≥ ρ₂(x)·ρ₂(y)
  have h1 := h₁ x y
  have h2 := h₂ x y
  calc ρ₁ (x ⊔ y) * ρ₂ (x ⊔ y) * (ρ₁ (x ⊓ y) * ρ₂ (x ⊓ y))
      = (ρ₁ (x ⊔ y) * ρ₁ (x ⊓ y)) * (ρ₂ (x ⊔ y) * ρ₂ (x ⊓ y)) := by ring
    _ ≥ (ρ₁ x * ρ₁ y) * (ρ₂ x * ρ₂ y) :=
        mul_le_mul h1 h2 (mul_nonneg (hnn₂ x) (hnn₂ y))
          (mul_nonneg (hnn₁ (x ⊔ y)) (hnn₁ (x ⊓ y)))
    _ = ρ₁ x * ρ₂ x * (ρ₁ y * ρ₂ y) := by ring

/-! ### Single-site functions

A function V : (ι → ℝ) → ℝ is *single-site* if it decomposes as
V(φ) = Σᵢ vᵢ(φᵢ). Such functions trivially satisfy the FKG lattice condition
because {max(a,b), min(a,b)} = {a, b} as sets. -/

/-- A function on `ι → ℝ` is *single-site* if it decomposes as a sum of
functions each depending on a single coordinate. This is the form of the
interaction potential in P(φ)₂ field theory. -/
def IsSingleSite (V : (ι → ℝ) → ℝ) : Prop :=
  ∃ v : ι → (ℝ → ℝ), ∀ φ : ι → ℝ, V φ = ∑ i, v i (φ i)

/-- Single-site functions v(a ⊔ b) + v(a ⊓ b) = v(a) + v(b). -/
theorem single_coord_sup_inf_sum (v : ℝ → ℝ) (a b : ℝ) :
    v (a ⊔ b) + v (a ⊓ b) = v a + v b := by
  by_cases h : a ≤ b
  · rw [sup_eq_right.mpr h, inf_eq_left.mpr h, add_comm]
  · push_neg at h
    rw [sup_eq_left.mpr (le_of_lt h), inf_eq_right.mpr (le_of_lt h)]

/-- `exp(-V)` satisfies the FKG lattice condition (with equality) when V is
a sum of single-site functions. -/
theorem fkg_lattice_condition_single_site (V : (ι → ℝ) → ℝ)
    (hV : IsSingleSite V) :
    FKGLatticeCondition (fun φ => Real.exp (-V φ)) := by
  obtain ⟨v, hv⟩ := hV
  intro x y
  -- V(x⊔y) + V(x⊓y) = V(x) + V(y) for single-site V
  have hsum : V (x ⊔ y) + V (x ⊓ y) = V x + V y := by
    simp only [hv]
    show ∑ i, v i ((x ⊔ y) i) + ∑ i, v i ((x ⊓ y) i) = ∑ i, v i (x i) + ∑ i, v i (y i)
    simp only [Pi.sup_apply, Pi.inf_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => single_coord_sup_inf_sum (v i) (x i) (y i))
  -- exp(-V(x⊔y)) * exp(-V(x⊓y)) = exp(-(V(x⊔y)+V(x⊓y)))
  rw [← Real.exp_add, ← Real.exp_add]
  exact le_of_eq (congr_arg _ (by linarith))

/-! ### Submodularity and FKG lattice condition

A function V : (ι → ℝ) → ℝ is *submodular* if V(x ⊔ y) + V(x ⊓ y) ≤ V(x) + V(y).
Equivalently, exp(-V) satisfies the FKG lattice condition. The key application
is to quadratic forms V(φ) = ½⟨φ, Qφ⟩ where Q has non-positive off-diagonal
entries (ferromagnetic/attractive coupling). -/

/-- A function on `ι → ℝ` is submodular if V(x ⊔ y) + V(x ⊓ y) ≤ V(x) + V(y). -/
def IsSubmodular {ι : Type*} (V : (ι → ℝ) → ℝ) : Prop :=
  ∀ x y : ι → ℝ, V (x ⊔ y) + V (x ⊓ y) ≤ V x + V y

/-- If V is submodular, then exp(-V) satisfies the FKG lattice condition. -/
theorem fkg_lattice_condition_of_submodular {ι : Type*} (V : (ι → ℝ) → ℝ)
    (hV : IsSubmodular V) :
    FKGLatticeCondition (fun φ => Real.exp (-V φ)) := by
  intro x y
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp_of_le (by linarith [hV x y])

/-- For any `a, b, c, d : ℝ`, the max-min product inequality:
`(a ⊔ b) * (c ⊔ d) + (a ⊓ b) * (c ⊓ d) ≥ a * c + b * d`. -/
theorem sup_inf_mul_add_le (a b c d : ℝ) :
    a * c + b * d ≤ (a ⊔ b) * (c ⊔ d) + (a ⊓ b) * (c ⊓ d) := by
  by_cases hab : a ≤ b <;> by_cases hcd : c ≤ d
  · rw [sup_eq_right.mpr hab, inf_eq_left.mpr hab, sup_eq_right.mpr hcd, inf_eq_left.mpr hcd]
    ring_nf; linarith
  · push_neg at hcd
    rw [sup_eq_right.mpr hab, inf_eq_left.mpr hab,
        sup_eq_left.mpr (le_of_lt hcd), inf_eq_right.mpr (le_of_lt hcd)]
    nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hcd) (sub_nonneg.mpr hab)]
  · push_neg at hab
    rw [sup_eq_left.mpr (le_of_lt hab), inf_eq_right.mpr (le_of_lt hab),
        sup_eq_right.mpr hcd, inf_eq_left.mpr hcd]
    nlinarith [mul_le_mul_of_nonneg_left hcd (sub_nonneg.mpr (le_of_lt hab))]
  · push_neg at hab hcd
    rw [sup_eq_left.mpr (le_of_lt hab), inf_eq_right.mpr (le_of_lt hab),
        sup_eq_left.mpr (le_of_lt hcd), inf_eq_right.mpr (le_of_lt hcd)]

/-- A quadratic form `V(φ) = ∑ x, ∑ y, Q x y * φ x * φ y` is submodular when
all off-diagonal entries of Q are non-positive.

Proof: The diagonal terms cancel (a² + b² = max² + min²). Each off-diagonal
pair (x,y) contributes `Q x y * [max·max + min·min - a·c - b·d]` which is
≤ 0 when Q x y ≤ 0 (by `sup_inf_mul_add_le`). -/
theorem quadraticForm_submodular_of_nonpos_offDiag
    {ι : Type*} [Fintype ι] (Q : ι → ι → ℝ)
    (hQ_offdiag : ∀ x y : ι, x ≠ y → Q x y ≤ 0) :
    IsSubmodular (fun φ : ι → ℝ => ∑ x, ∑ y, Q x y * φ x * φ y) := by
  intro a b
  simp only [Pi.sup_apply, Pi.inf_apply]
  -- We need: Σ Q(x,y) (a⊔b)_x (a⊔b)_y + Σ Q(x,y) (a⊓b)_x (a⊓b)_y
  --        ≤ Σ Q(x,y) a_x a_y + Σ Q(x,y) b_x b_y
  -- Split into diagonal (x=y) and off-diagonal (x≠y)
  -- Diagonal: Q(x,x)(max² + min²) = Q(x,x)(a² + b²) — equal
  -- Off-diagonal: Q(x,y)(max_x·max_y + min_x·min_y) ≥ Q(x,y)(a_x·a_y + b_x·b_y) when Q≤0
  suffices h : ∀ x y : ι, x ≠ y →
      Q x y * ((a x ⊔ b x) * (a y ⊔ b y)) + Q x y * ((a x ⊓ b x) * (a y ⊓ b y)) ≤
      Q x y * (a x * a y) + Q x y * (b x * b y) by
    calc ∑ x, ∑ y, Q x y * (a x ⊔ b x) * (a y ⊔ b y) +
         ∑ x, ∑ y, Q x y * (a x ⊓ b x) * (a y ⊓ b y)
        = ∑ x, ∑ y, (Q x y * ((a x ⊔ b x) * (a y ⊔ b y)) +
                      Q x y * ((a x ⊓ b x) * (a y ⊓ b y))) := by
          rw [← Finset.sum_add_distrib]; congr 1; ext x
          rw [← Finset.sum_add_distrib]; congr 1; ext y; ring
      _ ≤ ∑ x, ∑ y, (Q x y * (a x * a y) + Q x y * (b x * b y)) := by
          apply Finset.sum_le_sum; intro x _
          apply Finset.sum_le_sum; intro y _
          by_cases hxy : x = y
          · subst hxy
            have hsq : (a x ⊔ b x) * (a x ⊔ b x) + (a x ⊓ b x) * (a x ⊓ b x) =
                a x * a x + b x * b x := by
              by_cases h : a x ≤ b x
              · rw [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
              · push_neg at h
                rw [sup_eq_left.mpr (le_of_lt h), inf_eq_right.mpr (le_of_lt h)]
            have key : Q x x * ((a x ⊔ b x) * (a x ⊔ b x)) +
                Q x x * ((a x ⊓ b x) * (a x ⊓ b x)) =
                Q x x * (a x * a x) + Q x x * (b x * b x) := by
              rw [← mul_add, ← mul_add, hsq]
            linarith
          · exact h x y hxy
      _ = ∑ x, ∑ y, Q x y * a x * a y + ∑ x, ∑ y, Q x y * b x * b y := by
          rw [← Finset.sum_add_distrib]; congr 1; ext x
          rw [← Finset.sum_add_distrib]; congr 1; ext y; ring
  -- Prove the off-diagonal bound
  intro x y hxy
  have hQ := hQ_offdiag x y hxy
  have hmul := sup_inf_mul_add_le (a x) (b x) (a y) (b y)
  -- Q(x,y) ≤ 0 and max·max + min·min ≥ a·a + b·b
  -- So Q(x,y)·(max·max + min·min) ≤ Q(x,y)·(a·a + b·b)
  nlinarith

/-! ## Continuous Ahlswede-Daykin theorem and FKG

The core FKG theorem is proved via the **Continuous Ahlswede-Daykin** (Four Functions)
theorem. For nonneg integrable f₁, f₂, f₃, f₄ satisfying the pointwise condition
`f₁(x) · f₂(y) ≤ f₃(x ⊔ y) · f₄(x ⊓ y)`, we have `(∫f₁)(∫f₂) ≤ (∫f₃)(∫f₄)`.

FKG follows by setting f₁ = F·ρ, f₂ = G·ρ, f₃ = F·G·ρ, f₄ = ρ.

The proof proceeds by induction on dimension:
- **1D case**: Split ℝ² into {x ≤ y} and use the algebraic four-functions lemma.
- **Inductive step**: Integrate out one variable via Fubini. The 1D AD theorem
  applied to fibers shows the marginals satisfy AD. Apply the IH.

References: Ahlswede-Daykin (1978), Glimm-Jaffe §19. -/

/-- **Algebraic four-functions lemma.** If 0 ≤ u, v ≤ P and u·v ≤ P·Q
(with all values nonneg), then u + v ≤ P + Q.

Proof: if P = 0 then u = v = 0; if P > 0 then 0 ≤ (P-u)(P-v) gives
P(u+v) ≤ P² + uv ≤ P² + PQ = P(P+Q), divide by P. -/
lemma algebraic_four_functions {u v P Q : ℝ}
    (hu_nn : 0 ≤ u) (hv_nn : 0 ≤ v) (hP_nn : 0 ≤ P) (hQ_nn : 0 ≤ Q)
    (hu : u ≤ P) (hv : v ≤ P) (huv : u * v ≤ P * Q) :
    u + v ≤ P + Q := by
  by_cases hP : P = 0
  · have : u = 0 := le_antisymm (hP ▸ hu) hu_nn
    have : v = 0 := le_antisymm (hP ▸ hv) hv_nn
    simp [*]
  · have hP_pos : 0 < P := lt_of_le_of_ne hP_nn (Ne.symm hP)
    -- 0 ≤ (P - u)(P - v) = P² - P(u+v) + uv
    have h1 : 0 ≤ (P - u) * (P - v) := mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hv)
    -- P(u+v) ≤ P² + uv ≤ P² + PQ = P(P+Q)
    nlinarith

/-! ### 1D Ahlswede-Daykin

The 1D proof uses the pointwise sum bound from `algebraic_four_functions`:
for all x, y, `f₁(x)f₂(y) + f₁(y)f₂(x) ≤ f₃(x)f₄(y) + f₃(y)f₄(x)`.
Integrating over ℝ² and using symmetry gives `2(∫f₁)(∫f₂) ≤ 2(∫f₃)(∫f₄)`. -/

/-- **1D Continuous Ahlswede-Daykin theorem.**
For nonneg integrable f₁, f₂, f₃, f₄ : ℝ → ℝ satisfying the AD condition,
`(∫ f₁)(∫ f₂) ≤ (∫ f₃)(∫ f₄)`. -/
theorem ahlswede_daykin_one_dim
    (f₁ f₂ f₃ f₄ : ℝ → ℝ)
    (hnn₁ : ∀ x, 0 ≤ f₁ x) (hnn₂ : ∀ x, 0 ≤ f₂ x)
    (hnn₃ : ∀ x, 0 ≤ f₃ x) (hnn₄ : ∀ x, 0 ≤ f₄ x)
    (hAD : ∀ x y : ℝ, f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y))
    (hi₁ : Integrable f₁) (hi₂ : Integrable f₂)
    (hi₃ : Integrable f₃) (hi₄ : Integrable f₄) :
    (∫ x, f₁ x) * (∫ x, f₂ x) ≤ (∫ x, f₃ x) * (∫ x, f₄ x) := by
  -- Step 1: Pointwise sum bound via algebraic_four_functions
  have hpw : ∀ x y : ℝ,
      f₁ x * f₂ y + f₁ y * f₂ x ≤ f₃ x * f₄ y + f₃ y * f₄ x := by
    intro x y
    -- Apply algebraic_four_functions with u = f₁(x)f₂(y), v = f₁(y)f₂(x),
    -- P = f₃(x⊔y)f₄(x⊓y), Q = f₃(x⊓y)f₄(x⊔y)
    have hu_le : f₁ x * f₂ y ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y) := hAD x y
    have hv_le : f₁ y * f₂ x ≤ f₃ (x ⊔ y) * f₄ (x ⊓ y) := by
      have := hAD y x; rwa [sup_comm, inf_comm] at this
    have huv_le : (f₁ x * f₂ y) * (f₁ y * f₂ x) ≤
        (f₃ (x ⊔ y) * f₄ (x ⊓ y)) * (f₃ (x ⊓ y) * f₄ (x ⊔ y)) := by
      have hux := hAD x x; simp only [sup_idem, inf_idem] at hux
      have huy := hAD y y; simp only [sup_idem, inf_idem] at huy
      -- uv = (f₁x·f₂x)(f₁y·f₂y) ≤ (f₃x·f₄x)(f₃y·f₄y) = PQ
      have : (f₁ x * f₂ y) * (f₁ y * f₂ x) = (f₁ x * f₂ x) * (f₁ y * f₂ y) := by ring
      rw [this]
      have : (f₃ (x ⊔ y) * f₄ (x ⊓ y)) * (f₃ (x ⊓ y) * f₄ (x ⊔ y)) =
          (f₃ x * f₄ x) * (f₃ y * f₄ y) := by
        by_cases h : x ≤ y
        · simp only [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
        · push_neg at h
          simp only [sup_eq_left.mpr (le_of_lt h), inf_eq_right.mpr (le_of_lt h)]; ring
      rw [this]
      exact mul_le_mul hux huy (mul_nonneg (hnn₁ y) (hnn₂ y))
        (mul_nonneg (hnn₃ x) (hnn₄ x))
    have hab := algebraic_four_functions
      (mul_nonneg (hnn₁ x) (hnn₂ y)) (mul_nonneg (hnn₁ y) (hnn₂ x))
      (mul_nonneg (hnn₃ _) (hnn₄ _)) (mul_nonneg (hnn₃ _) (hnn₄ _))
      hu_le hv_le huv_le
    -- P + Q = f₃(x)f₄(y) + f₃(y)f₄(x) since {x⊔y, x⊓y} = {x, y}
    have hPQ : f₃ (x ⊔ y) * f₄ (x ⊓ y) + f₃ (x ⊓ y) * f₄ (x ⊔ y) =
        f₃ x * f₄ y + f₃ y * f₄ x := by
      by_cases h : x ≤ y
      · simp only [sup_eq_right.mpr h, inf_eq_left.mpr h]; ring
      · push_neg at h
        simp only [sup_eq_left.mpr (le_of_lt h), inf_eq_right.mpr (le_of_lt h)]
    linarith
  -- Step 2: Integrate the pointwise sum bound over ℝ².
  -- Integrability of product functions
  have hi₁₂ : Integrable (fun p : ℝ × ℝ => f₁ p.1 * f₂ p.2) (volume.prod volume) :=
    hi₁.mul_prod hi₂
  have hi₂₁ : Integrable (fun p : ℝ × ℝ => f₁ p.2 * f₂ p.1) (volume.prod volume) :=
    (hi₂.mul_prod hi₁).congr (ae_of_all _ fun p => by ring)
  have hi₃₄ : Integrable (fun p : ℝ × ℝ => f₃ p.1 * f₄ p.2) (volume.prod volume) :=
    hi₃.mul_prod hi₄
  have hi₄₃ : Integrable (fun p : ℝ × ℝ => f₃ p.2 * f₄ p.1) (volume.prod volume) :=
    (hi₄.mul_prod hi₃).congr (ae_of_all _ fun p => by ring)
  -- Integrate: ∫∫ (LHS sum) ≤ ∫∫ (RHS sum)
  have hint := integral_mono (hi₁₂.add hi₂₁) (hi₃₄.add hi₄₃)
    (fun p => hpw p.1 p.2)
  -- Evaluate each double integral as product of single integrals
  -- ∫∫ f₁(x)f₂(y) = (∫f₁)(∫f₂)
  have h12 : ∫ p : ℝ × ℝ, f₁ p.1 * f₂ p.2 ∂(volume.prod volume) =
      (∫ x, f₁ x) * (∫ x, f₂ x) := integral_prod_mul f₁ f₂
  -- ∫∫ f₁(y)f₂(x) = (∫f₂)(∫f₁) = (∫f₁)(∫f₂)
  have h21 : ∫ p : ℝ × ℝ, f₁ p.2 * f₂ p.1 ∂(volume.prod volume) =
      (∫ x, f₁ x) * (∫ x, f₂ x) := by
    rw [show (fun p : ℝ × ℝ => f₁ p.2 * f₂ p.1) =
        (fun p : ℝ × ℝ => f₂ p.1 * f₁ p.2) from funext fun p => by ring]
    rw [integral_prod_mul f₂ f₁]; ring
  have h34 : ∫ p : ℝ × ℝ, f₃ p.1 * f₄ p.2 ∂(volume.prod volume) =
      (∫ x, f₃ x) * (∫ x, f₄ x) := integral_prod_mul f₃ f₄
  have h43 : ∫ p : ℝ × ℝ, f₃ p.2 * f₄ p.1 ∂(volume.prod volume) =
      (∫ x, f₃ x) * (∫ x, f₄ x) := by
    rw [show (fun p : ℝ × ℝ => f₃ p.2 * f₄ p.1) =
        (fun p : ℝ × ℝ => f₄ p.1 * f₃ p.2) from funext fun p => by ring]
    rw [integral_prod_mul f₄ f₃]; ring
  -- Combine: hint says ∫(LHS sum) ≤ ∫(RHS sum), rewrite to product form
  have hlhs_eq : ∫ p : ℝ × ℝ, (f₁ p.1 * f₂ p.2 + f₁ p.2 * f₂ p.1) ∂(volume.prod volume) =
      2 * ((∫ x, f₁ x) * (∫ x, f₂ x)) := by
    rw [integral_add hi₁₂ hi₂₁, h12, h21]; ring
  have hrhs_eq : ∫ p : ℝ × ℝ, (f₃ p.1 * f₄ p.2 + f₃ p.2 * f₄ p.1) ∂(volume.prod volume) =
      2 * ((∫ x, f₃ x) * (∫ x, f₄ x)) := by
    rw [integral_add hi₃₄ hi₄₃, h34, h43]; ring
  have hint' : 2 * ((∫ x, f₁ x) * (∫ x, f₂ x)) ≤
      2 * ((∫ x, f₃ x) * (∫ x, f₄ x)) := by
    calc 2 * ((∫ x, f₁ x) * (∫ x, f₂ x))
        = ∫ p : ℝ × ℝ, (f₁ p.1 * f₂ p.2 + f₁ p.2 * f₂ p.1) ∂(volume.prod volume) :=
          hlhs_eq.symm
      _ ≤ ∫ p : ℝ × ℝ, (f₃ p.1 * f₄ p.2 + f₃ p.2 * f₄ p.1) ∂(volume.prod volume) := by
          exact integral_mono (hi₁₂.add hi₂₁) (hi₃₄.add hi₄₃) (fun p => hpw p.1 p.2)
      _ = 2 * ((∫ x, f₃ x) * (∫ x, f₄ x)) := hrhs_eq
  linarith

/-! ### Fubini decomposition axioms

Textbook results about Fubini decomposition of integrals over `(ι → ℝ)`.
These will be proved separately using `MeasurableEquiv.piFinSuccAbove` and
`volume_preserving_piFinSuccAbove` from Mathlib. -/

/-- Fubini decomposition: for `i : ι`, the integral over `(ι → ℝ)` decomposes
as an iterated integral over `ℝ` and `{j // j ≠ i} → ℝ`.

Here `Function.update x' i t` denotes the function that agrees with `x'`
except at coordinate `i` where it takes value `t`. -/
axiom fubini_pi_decomp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : Integrable f) (i : ι) :
    ∫ x, f x = ∫ x' : {j : ι // j ≠ i} → ℝ,
      (∫ t : ℝ, f (fun j => if h : j = i then t else x' ⟨j, h⟩)) ∂volume

/-- The marginal (integral over one coordinate) of an integrable nonneg
function is integrable. -/
axiom integrable_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : Integrable f) (hnn : ∀ x, 0 ≤ f x) (i : ι) :
    Integrable (fun x' : {j : ι // j ≠ i} → ℝ =>
      ∫ t : ℝ, f (fun j => if h : j = i then t else x' ⟨j, h⟩))

/-- The fiber function (fixing all but one coordinate) is integrable for a.e.
value of the remaining coordinates. This is a consequence of Fubini's theorem:
if `f` is integrable over the product, then for a.e. slice the fiber is integrable. -/
axiom integrable_fiber_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (hf : Integrable f) (i : ι) :
    ∀ᵐ x' : {j : ι // j ≠ i} → ℝ,
      Integrable (fun t : ℝ => f (fun j => if h : j = i then t else x' ⟨j, h⟩))

/-- The integral over an empty type is the function value at the unique point.
Volume on `(Empty → ℝ)` is a probability measure. -/
axiom integral_empty_pi (f : (Empty → ℝ) → ℝ) :
    ∫ x, f x = f (fun e => e.elim)

/-! ### Sup/inf compatibility with coordinate decomposition -/

/-- Componentwise sup commutes with coordinate insertion. -/
lemma sup_dite_eq {ι : Type*} [DecidableEq ι] (i : ι)
    (t s : ℝ) (x' y' : {j : ι // j ≠ i} → ℝ) :
    (fun j => if h : j = i then t else x' ⟨j, h⟩) ⊔
    (fun j => if h : j = i then s else y' ⟨j, h⟩) =
    (fun j => if h : j = i then (t ⊔ s) else (x' ⊔ y') ⟨j, h⟩) := by
  ext j
  simp only [Pi.sup_apply]
  split <;> simp [Pi.sup_apply]

/-- Componentwise inf commutes with coordinate insertion. -/
lemma inf_dite_eq {ι : Type*} [DecidableEq ι] (i : ι)
    (t s : ℝ) (x' y' : {j : ι // j ≠ i} → ℝ) :
    (fun j => if h : j = i then t else x' ⟨j, h⟩) ⊓
    (fun j => if h : j = i then s else y' ⟨j, h⟩) =
    (fun j => if h : j = i then (t ⊓ s) else (x' ⊓ y') ⟨j, h⟩) := by
  ext j
  simp only [Pi.inf_apply]
  split <;> simp [Pi.inf_apply]

/-! ### n-dimensional Ahlswede-Daykin by induction -/

/-- AD condition preserved by marginalization (a.e. version). The 1D AD theorem
applied to fibers shows that integrating out one coordinate preserves the AD
condition. Since fiber integrability only holds a.e. (by Fubini), the AD
condition on marginals holds for a.e. `(x', y')` in the product.

Proof outline: By `integrable_fiber_ae`, for a.e. x' the fiber of each f_k
at x' is integrable. Since x'⊔y' and x'⊓y' are measurable functions of
(x', y'), the set of pairs where any of the four fibers (at x', y', x'⊔y',
x'⊓y') fails to be integrable has product measure zero. For "good" pairs,
`ahlswede_daykin_one_dim` applies to the four fiber functions, giving the
marginal AD inequality. -/
axiom ad_marginal_preservation_ae {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f₁ f₂ f₃ f₄ : (ι → ℝ) → ℝ)
    (hnn₁ : ∀ x, 0 ≤ f₁ x) (hnn₂ : ∀ x, 0 ≤ f₂ x)
    (hnn₃ : ∀ x, 0 ≤ f₃ x) (hnn₄ : ∀ x, 0 ≤ f₄ x)
    (hAD : ∀ᵐ p : (ι → ℝ) × (ι → ℝ),
      f₁ p.1 * f₂ p.2 ≤ f₃ (p.1 ⊔ p.2) * f₄ (p.1 ⊓ p.2))
    (hi₁ : Integrable f₁) (hi₂ : Integrable f₂)
    (hi₃ : Integrable f₃) (hi₄ : Integrable f₄) (i : ι) :
    let marg (f : (ι → ℝ) → ℝ) (x' : {j : ι // j ≠ i} → ℝ) :=
      ∫ t, f (fun j => if h : j = i then t else x' ⟨j, h⟩)
    ∀ᵐ p : ({j : ι // j ≠ i} → ℝ) × ({j : ι // j ≠ i} → ℝ),
      marg f₁ p.1 * marg f₂ p.2 ≤ marg f₃ (p.1 ⊔ p.2) * marg f₄ (p.1 ⊓ p.2)

/-- **n-dimensional Ahlswede-Daykin theorem.**
For nonneg integrable f₁, f₂, f₃, f₄ on `(ι → ℝ)` satisfying the AD condition
`f₁(x)·f₂(y) ≤ f₃(x⊔y)·f₄(x⊓y)` a.e. in the product, we have
`(∫f₁)(∫f₂) ≤ (∫f₃)(∫f₄)`.

The AD condition is stated a.e. because the Fubini induction produces marginals
satisfying the AD condition only a.e. (fiber integrability holds a.e. by Fubini).

Proof by induction on `Fintype.card ι` using Fubini + 1D AD on fibers. -/
theorem ahlswede_daykin : ∀ (n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι],
    Fintype.card ι = n →
    ∀ (f₁ f₂ f₃ f₄ : (ι → ℝ) → ℝ),
    (∀ x, 0 ≤ f₁ x) → (∀ x, 0 ≤ f₂ x) →
    (∀ x, 0 ≤ f₃ x) → (∀ x, 0 ≤ f₄ x) →
    (∀ᵐ p : (ι → ℝ) × (ι → ℝ), f₁ p.1 * f₂ p.2 ≤ f₃ (p.1 ⊔ p.2) * f₄ (p.1 ⊓ p.2)) →
    Integrable f₁ → Integrable f₂ →
    Integrable f₃ → Integrable f₄ →
    (∫ x, f₁ x) * (∫ x, f₂ x) ≤ (∫ x, f₃ x) * (∫ x, f₄ x) := by
  intro n
  induction n with
  | zero =>
    intro ι _ _ hcard f₁ f₂ f₃ f₄ hnn₁ hnn₂ hnn₃ hnn₄ hAD _ _ _ _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    haveI : Unique (ι → ℝ) := Pi.uniqueOfIsEmpty _
    simp only [integral_unique, smul_eq_mul]
    -- Fix the Inhabited instance to match integral_unique's default
    -- (avoids Pi.instInhabited vs Unique.instInhabited diamond)
    have hsub : ∀ (a b : ι → ℝ), a = b := fun a b => Subsingleton.elim a b
    set V := (volume : Measure (ι → ℝ)).real Set.univ with hV_def
    by_cases hmu : (volume : Measure (ι → ℝ)) = 0
    · -- volume = 0 ⟹ V = 0 ⟹ both sides are 0
      have hV : V = 0 := by simp [hV_def, Measure.real, hmu]
      simp [hV]
    · -- Extract pointwise inequality from a.e. condition
      haveI : NeZero (volume : Measure (ι → ℝ)) := ⟨hmu⟩
      -- Use the Unique default to match integral_unique's output
      set d := @default (ι → ℝ) Unique.instInhabited with hd_def
      have had_pt : f₁ d * f₂ d ≤ f₃ d * f₄ d :=
        Filter.eventually_const.mp
          (hAD.mono fun p hp => by
            have h1 : p.1 = d := Subsingleton.elim _ _
            have h2 : p.2 = d := Subsingleton.elim _ _
            simp only [h1, h2, sup_idem, inf_idem] at hp
            exact hp)
      have h_eq : V * f₃ d * (V * f₄ d) -
          V * f₁ d * (V * f₂ d) =
          V ^ 2 * (f₃ d * f₄ d - f₁ d * f₂ d) := by ring
      have key : 0 ≤ V * f₃ d * (V * f₄ d) -
          V * f₁ d * (V * f₂ d) := by
        rw [h_eq]; exact mul_nonneg (sq_nonneg V) (sub_nonneg.mpr had_pt)
      linarith
  | succ n ih =>
    intro ι inst_fin inst_dec hcard f₁ f₂ f₃ f₄ hnn₁ hnn₂ hnn₃ hnn₄ hAD hi₁ hi₂ hi₃ hi₄
    -- Pick a coordinate i : ι (ι is nonempty since card > 0)
    have hne : Nonempty ι := by
      rw [← Fintype.card_pos_iff, hcard]; exact Nat.succ_pos _
    let i : ι := Classical.choice hne
    -- Define marginals: marg(f)(x') = ∫ f(insert i t x') dt
    set marg := fun (f : (ι → ℝ) → ℝ) (x' : {j : ι // j ≠ i} → ℝ) =>
      ∫ t, f (fun j => if h : j = i then t else x' ⟨j, h⟩) with hmarg_def
    -- Fubini: ∫ f = ∫ marg(f) for each f_k
    have hfub : ∀ f : (ι → ℝ) → ℝ, Integrable f →
        ∫ x, f x = ∫ x', marg f x' := by
      intro f hf
      exact fubini_pi_decomp f hf i
    rw [hfub f₁ hi₁, hfub f₂ hi₂, hfub f₃ hi₃, hfub f₄ hi₄]
    -- The marginals satisfy the AD condition a.e. (by ad_marginal_preservation_ae)
    have hmarg_ad := ad_marginal_preservation_ae f₁ f₂ f₃ f₄
      hnn₁ hnn₂ hnn₃ hnn₄ hAD hi₁ hi₂ hi₃ hi₄ i
    -- Card of {j // j ≠ i} = n
    have hcard' : Fintype.card {j : ι // j ≠ i} = n := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hcard]
      simp
    -- Apply IH to the marginals on {j // j ≠ i} → ℝ
    exact ih hcard'
      (marg f₁) (marg f₂) (marg f₃) (marg f₄)
      (fun x' => integral_nonneg (fun t => hnn₁ _))
      (fun x' => integral_nonneg (fun t => hnn₂ _))
      (fun x' => integral_nonneg (fun t => hnn₃ _))
      (fun x' => integral_nonneg (fun t => hnn₄ _))
      hmarg_ad
      (integrable_marginal f₁ hi₁ hnn₁ i)
      (integrable_marginal f₂ hi₂ hnn₂ i)
      (integrable_marginal f₃ hi₃ hnn₃ i)
      (integrable_marginal f₄ hi₄ hnn₄ i)

/-! ### FKG as corollary of Ahlswede-Daykin

The FKG inequality `(∫FGρ)(∫ρ) ≥ (∫Fρ)(∫Gρ)` is shift-invariant in F and G:
replacing F by F + c doesn't change the LHS − RHS. So it suffices to prove
FKG for nonneg F, G. For nonneg monotone F, G, set f₁ = F·ρ, f₂ = G·ρ,
f₃ = F·G·ρ, f₄ = ρ and apply Ahlswede-Daykin. -/

/-- **FKG for nonneg monotone functions** via Ahlswede-Daykin. -/
theorem fkg_from_lattice_condition_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lattice : FKGLatticeCondition ρ)
    (F G : (ι → ℝ) → ℝ) (hF : Monotone F) (hG : Monotone G)
    (hF_nn : ∀ x, 0 ≤ F x) (hG_nn : ∀ x, 0 ≤ G x)
    (hρi : Integrable ρ)
    (hFρi : Integrable (fun φ => F φ * ρ φ))
    (hGρi : Integrable (fun φ => G φ * ρ φ))
    (hFGρi : Integrable (fun φ => F φ * G φ * ρ φ)) :
    (∫ φ, F φ * G φ * ρ φ) * (∫ φ, ρ φ) ≥
    (∫ φ, F φ * ρ φ) * (∫ φ, G φ * ρ φ) := by
  -- Apply AD with f₁ = F·ρ, f₂ = G·ρ, f₃ = F·G·ρ, f₄ = ρ
  have had : ∀ x y : ι → ℝ,
      (F x * ρ x) * (G y * ρ y) ≤
      (F (x ⊔ y) * G (x ⊔ y) * ρ (x ⊔ y)) * ρ (x ⊓ y) := by
    intro x y
    -- F(x) ≤ F(x⊔y), G(y) ≤ G(x⊔y) by monotonicity (x ≤ x⊔y, y ≤ x⊔y)
    have hFx := hF (le_sup_left : x ≤ x ⊔ y)
    have hGy := hG (le_sup_right : y ≤ x ⊔ y)
    -- ρ(x)ρ(y) ≤ ρ(x⊔y)ρ(x⊓y) by FKG lattice condition
    have hρxy := hρ_lattice x y
    -- Combine: F(x)G(y) ≤ F(x⊔y)G(x⊔y) and ρ(x)ρ(y) ≤ ρ(x⊔y)ρ(x⊓y)
    have hFG : F x * G y ≤ F (x ⊔ y) * G (x ⊔ y) :=
      mul_le_mul hFx hGy (hG_nn y) (le_trans (hF_nn x) hFx)
    have hFG_nn : 0 ≤ F (x ⊔ y) * G (x ⊔ y) :=
      mul_nonneg (le_trans (hF_nn x) hFx) (le_trans (hG_nn y) hGy)
    nlinarith [mul_nonneg (hρ_nn x) (hρ_nn y)]
  -- Apply AD theorem
  exact ahlswede_daykin (Fintype.card ι) rfl
    (fun φ => F φ * ρ φ) (fun φ => G φ * ρ φ)
    (fun φ => F φ * G φ * ρ φ) ρ
    (fun x => mul_nonneg (hF_nn x) (hρ_nn x))
    (fun x => mul_nonneg (hG_nn x) (hρ_nn x))
    (fun x => mul_nonneg (mul_nonneg (hF_nn x) (hG_nn x)) (hρ_nn x))
    hρ_nn (Filter.Eventually.of_forall fun p => had p.1 p.2) hFρi hGρi hFGρi hρi

/-! ### Truncation lemmas for general FKG

The FKG expression `(∫FGρ)(∫ρ) − (∫Fρ)(∫Gρ)` is invariant under
shifting F by a constant. Truncating F at level −n and shifting by n gives
a nonneg monotone function. Apply `fkg_from_lattice_condition_nonneg`, then
take n → ∞ by dominated convergence. -/

/-- Truncation of a monotone function: `max(F, -(n:ℝ))` is monotone. -/
lemma monotone_max_neg (F : (ι → ℝ) → ℝ) (hF : Monotone F) (n : ℝ) :
    Monotone (fun x => F x ⊔ (-n)) :=
  fun _ _ hle => sup_le_sup_right (hF hle) _

/-- |max(F(x), -n)| ≤ |F(x)| + n for any x. More precisely, for the
truncation argument, |max(F, -n)| ≤ max(|F|, n). -/
lemma abs_max_neg_le (a n : ℝ) (hn : 0 ≤ n) : |a ⊔ (-n)| ≤ |a| + n := by
  rcases le_or_gt a (-n) with h | h
  · rw [sup_eq_right.mpr h]; rw [abs_of_nonpos (by linarith)]; linarith [abs_nonneg a]
  · rw [sup_eq_left.mpr (le_of_lt h)]; linarith [le_abs_self a]

/-- Dominated convergence for the FKG truncation argument. For monotone F,
`max(F, -n) + n` is nonneg and monotone, and `max(F, -n) → F` pointwise.
If F·ρ is integrable, then ∫ max(F,-n)·ρ → ∫ F·ρ by DCT. -/
axiom fkg_truncation_dct {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℝ) (ρ : (ι → ℝ) → ℝ)
    (hFρi : Integrable (fun φ => F φ * ρ φ)) (hρ_nn : ∀ x, 0 ≤ ρ x) :
    Filter.Tendsto (fun n : ℕ => ∫ φ, (F φ ⊔ (-(n : ℝ))) * ρ φ)
      Filter.atTop (nhds (∫ φ, F φ * ρ φ))

/-- DCT for the product F·G truncated. -/
axiom fkg_truncation_dct_prod {ι : Type*} [Fintype ι]
    (F G : (ι → ℝ) → ℝ) (ρ : (ι → ℝ) → ℝ)
    (hFGρi : Integrable (fun φ => F φ * G φ * ρ φ)) (hρ_nn : ∀ x, 0 ≤ ρ x) :
    Filter.Tendsto
      (fun n : ℕ => ∫ φ, (F φ ⊔ (-(n : ℝ))) * (G φ ⊔ (-(n : ℝ))) * ρ φ)
      Filter.atTop (nhds (∫ φ, F φ * G φ * ρ φ))

/-- Integrability of truncated functions. -/
axiom integrable_truncation_mul {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℝ) (ρ : (ι → ℝ) → ℝ) (n : ℕ)
    (hFρi : Integrable (fun φ => F φ * ρ φ)) :
    Integrable (fun φ => (F φ ⊔ (-(n : ℝ))) * ρ φ)

axiom integrable_truncation_prod_mul {ι : Type*} [Fintype ι]
    (F G : (ι → ℝ) → ℝ) (ρ : (ι → ℝ) → ℝ) (n : ℕ)
    (hFGρi : Integrable (fun φ => F φ * G φ * ρ φ)) :
    Integrable (fun φ => (F φ ⊔ (-(n : ℝ))) * (G φ ⊔ (-(n : ℝ))) * ρ φ)

theorem fkg_from_lattice_condition {ι : Type*} [Fintype ι]
    (ρ : (ι → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lattice : FKGLatticeCondition ρ)
    (F G : (ι → ℝ) → ℝ) (hF : Monotone F) (hG : Monotone G)
    (hρi : Integrable ρ)
    (hFρi : Integrable (fun φ => F φ * ρ φ))
    (hGρi : Integrable (fun φ => G φ * ρ φ))
    (hFGρi : Integrable (fun φ => F φ * G φ * ρ φ)) :
    (∫ φ, F φ * G φ * ρ φ) * (∫ φ, ρ φ) ≥
    (∫ φ, F φ * ρ φ) * (∫ φ, G φ * ρ φ) := by
  classical
  -- Truncate: Fn(x) = max(F(x), -n) + n, Gn(x) = max(G(x), -n) + n
  -- These are nonneg and monotone.
  -- The FKG expression is shift-invariant: replacing F by F+c doesn't change
  -- (∫FGρ)(∫ρ) - (∫Fρ)(∫Gρ). So FKG for (Fn, Gn) ↔ FKG for (max(F,-n), max(G,-n)).
  -- For each n, apply fkg_from_lattice_condition_nonneg to (Fn, Gn).
  -- Take n → ∞ using dominated convergence.
  set Fn := fun (n : ℕ) (x : ι → ℝ) => F x ⊔ (-(n : ℝ)) with hFn_def
  set Gn := fun (n : ℕ) (x : ι → ℝ) => G x ⊔ (-(n : ℝ)) with hGn_def
  -- For each n: FKG holds for Fn + n, Gn + n (nonneg, monotone)
  -- Shift invariance gives: FKG for Fn, Gn (possibly negative but bounded below)
  have hfkg_n : ∀ n : ℕ,
      (∫ φ, Fn n φ * Gn n φ * ρ φ) * (∫ φ, ρ φ) ≥
      (∫ φ, Fn n φ * ρ φ) * (∫ φ, Gn n φ * ρ φ) := by
    intro n
    -- Fn + n and Gn + n are nonneg and monotone
    set F' := fun x => Fn n x + (n : ℝ) with hF'_def
    set G' := fun x => Gn n x + (n : ℝ) with hG'_def
    have hF'_nn : ∀ x, 0 ≤ F' x := by
      intro x; simp only [hF'_def, hFn_def]; linarith [le_sup_right (a := F x) (b := -(n : ℝ))]
    have hG'_nn : ∀ x, 0 ≤ G' x := by
      intro x; simp only [hG'_def, hGn_def]; linarith [le_sup_right (a := G x) (b := -(n : ℝ))]
    have hF'_mono : Monotone F' := by
      intro a b hab; simp only [hF'_def, hFn_def]
      linarith [sup_le_sup_right (hF hab) (-(n : ℝ))]
    have hG'_mono : Monotone G' := by
      intro a b hab; simp only [hG'_def, hGn_def]
      linarith [sup_le_sup_right (hG hab) (-(n : ℝ))]
    -- FKG for F', G' (nonneg version)
    have h := fkg_from_lattice_condition_nonneg ρ hρ_nn hρ_lattice F' G'
      hF'_mono hG'_mono hF'_nn hG'_nn hρi
      (by -- Integrable (F'·ρ) = Integrable ((Fn n + n) · ρ)
        have : (fun φ => F' φ * ρ φ) = fun φ => Fn n φ * ρ φ + ↑n * ρ φ :=
          funext fun φ => by simp only [hF'_def]; ring
        rw [this]; exact (integrable_truncation_mul F ρ n hFρi).add (hρi.const_mul _))
      (by -- Integrable (G'·ρ)
        have : (fun φ => G' φ * ρ φ) = fun φ => Gn n φ * ρ φ + ↑n * ρ φ :=
          funext fun φ => by simp only [hG'_def]; ring
        rw [this]; exact (integrable_truncation_mul G ρ n hGρi).add (hρi.const_mul _))
      (by -- Integrable (F'·G'·ρ): expand (Fn+n)(Gn+n)ρ, each term integrable
        have hint : Integrable (fun φ => Fn n φ * Gn n φ * ρ φ + ↑n * (Fn n φ * ρ φ) +
            (↑n * (Gn n φ * ρ φ) + ↑n * ↑n * ρ φ)) :=
          ((integrable_truncation_prod_mul F G ρ n hFGρi).add
            ((integrable_truncation_mul F ρ n hFρi).const_mul ↑n)).add
            (((integrable_truncation_mul G ρ n hGρi).const_mul ↑n).add
              (hρi.const_mul (↑n * ↑n)))
        exact hint.congr (ae_of_all _ fun φ => by
          simp only [hFn_def, hGn_def]; ring))
    -- Shift invariance: rewrite integrals of F', G' in terms of Fn, Gn
    have hFn_int := integrable_truncation_mul F ρ n hFρi
    have hGn_int := integrable_truncation_mul G ρ n hGρi
    -- Shift invariance: rewrite h from F'/G' to Fn/Gn integrals
    -- Create integrability hypotheses matching the Fn/Gn aliases
    have hFn_int : Integrable (fun φ => Fn n φ * ρ φ) :=
      integrable_truncation_mul F ρ n hFρi
    have hGn_int : Integrable (fun φ => Gn n φ * ρ φ) :=
      integrable_truncation_mul G ρ n hGρi
    have hFGn_int : Integrable (fun φ => Fn n φ * Gn n φ * ρ φ) :=
      integrable_truncation_prod_mul F G ρ n hFGρi
    -- ∫ F'·ρ = ∫ Fn·ρ + n·∫ρ
    have hiFρ : (∫ φ, F' φ * ρ φ) = (∫ φ, Fn n φ * ρ φ) + ↑n * (∫ φ, ρ φ) := by
      trans ∫ φ, (Fn n φ * ρ φ + ↑n * ρ φ)
      · congr 1; ext φ; simp only [hF'_def]; ring
      · rw [integral_add hFn_int (hρi.const_mul _), integral_const_mul]
    have hiGρ : (∫ φ, G' φ * ρ φ) = (∫ φ, Gn n φ * ρ φ) + ↑n * (∫ φ, ρ φ) := by
      trans ∫ φ, (Gn n φ * ρ φ + ↑n * ρ φ)
      · congr 1; ext φ; simp only [hG'_def]; ring
      · rw [integral_add hGn_int (hρi.const_mul _), integral_const_mul]
    have hi_nFρ : Integrable (fun φ => ↑n * (Fn n φ * ρ φ)) := hFn_int.const_mul _
    have hi_nGρ : Integrable (fun φ => ↑n * (Gn n φ * ρ φ)) := hGn_int.const_mul _
    have hi_nnρ : Integrable (fun φ => ↑n * ↑n * ρ φ) := hρi.const_mul _
    have hi_ab : Integrable (fun φ => Fn n φ * Gn n φ * ρ φ + ↑n * (Fn n φ * ρ φ)) :=
      hFGn_int.add hi_nFρ
    have hi_cd : Integrable (fun φ => ↑n * (Gn n φ * ρ φ) + ↑n * ↑n * ρ φ) :=
      hi_nGρ.add hi_nnρ
    have hiFGρ : (∫ φ, F' φ * G' φ * ρ φ) =
        (∫ φ, Fn n φ * Gn n φ * ρ φ) + ↑n * (∫ φ, Fn n φ * ρ φ) +
        ↑n * (∫ φ, Gn n φ * ρ φ) + ↑n * ↑n * (∫ φ, ρ φ) := by
      trans ∫ φ, (Fn n φ * Gn n φ * ρ φ + ↑n * (Fn n φ * ρ φ) +
        (↑n * (Gn n φ * ρ φ) + ↑n * ↑n * ρ φ))
      · congr 1; ext φ; simp only [hF'_def, hG'_def]; ring
      · rw [integral_add hi_ab hi_cd]
        rw [integral_add hFGn_int hi_nFρ]
        rw [integral_add hi_nGρ hi_nnρ]
        simp only [integral_const_mul]; ring
    -- Cross terms cancel: (a+nb+nc+n²d)·d - (b+nd)·(c+nd) = a·d - b·c
    rw [hiFρ, hiGρ, hiFGρ] at h; nlinarith
  -- Take n → ∞ by dominated convergence
  have h_lim₁ := fkg_truncation_dct F ρ hFρi hρ_nn
  have h_lim₂ := fkg_truncation_dct G ρ hGρi hρ_nn
  have h_lim₃ := fkg_truncation_dct_prod F G ρ hFGρi hρ_nn
  -- The sequence sₙ = (∫FnGnρ)(∫ρ) - (∫Fnρ)(∫Gnρ) ≥ 0 for all n
  -- Use Fn/Gn aliases to match hfkg_n
  simp only [hFn_def, hGn_def] at hfkg_n
  have h_seq_nn : ∀ n : ℕ, (0 : ℝ) ≤
      (∫ φ, (F φ ⊔ (-(n : ℝ))) * (G φ ⊔ (-(n : ℝ))) * ρ φ) * (∫ φ, ρ φ) -
      (∫ φ, (F φ ⊔ (-(n : ℝ))) * ρ φ) * (∫ φ, (G φ ⊔ (-(n : ℝ))) * ρ φ) :=
    fun n => by linarith [hfkg_n n]
  -- The limit of sₙ is (∫FGρ)(∫ρ) - (∫Fρ)(∫Gρ)
  have h_tendsto : Filter.Tendsto
      (fun n : ℕ => (∫ φ, (F φ ⊔ (-(n : ℝ))) * (G φ ⊔ (-(n : ℝ))) * ρ φ) * (∫ φ, ρ φ) -
        (∫ φ, (F φ ⊔ (-(n : ℝ))) * ρ φ) * (∫ φ, (G φ ⊔ (-(n : ℝ))) * ρ φ))
      Filter.atTop
      (nhds ((∫ φ, F φ * G φ * ρ φ) * (∫ φ, ρ φ) -
        (∫ φ, F φ * ρ φ) * (∫ φ, G φ * ρ φ))) :=
    (h_lim₃.mul_const _).sub (h_lim₁.mul h_lim₂)
  -- Pass to the limit: 0 ≤ sₙ for all n → 0 ≤ lim sₙ
  linarith [ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h_seq_nn)]

/-! ## Application to lattice Gaussian measures -/

variable (d N : ℕ) [NeZero N]

/-! ### Monotonicity on Configuration space -/

/-- A function on configurations is *FKG-monotone* if it is increasing
with respect to pointwise ordering of field values at lattice sites:
whenever `ω₁(δ_x) ≤ ω₂(δ_x)` for all sites x, then `F(ω₁) ≤ F(ω₂)`. -/
def IsFieldMonotone (F : Configuration (FinLatticeField d N) → ℝ) : Prop :=
  ∀ ω₁ ω₂ : Configuration (FinLatticeField d N),
    (∀ x : FinLatticeSites d N, ω₁ (finLatticeDelta d N x) ≤ ω₂ (finLatticeDelta d N x)) →
    F ω₁ ≤ F ω₂

/-- Basis decomposition: any field configuration is a linear combination
of delta functions. -/
private lemma field_basis_decomposition (φ : FinLatticeField d N) :
    φ = ∑ y : FinLatticeSites d N, φ y • finLatticeDelta d N y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-! ### Field-Configuration correspondence

In finite dimensions, a configuration ω ∈ E* is uniquely determined by its
values on the basis {δ_x}. The map `liftToConfig` reconstructs ω from field
values φ(x). -/

/-- Lift field values to a configuration (continuous linear functional).
Given `φ : FinLatticeField d N`, constructs the CLM `f ↦ ∑ x, f(x) · φ(x)`. -/
private def liftToConfig (φ : FinLatticeField d N) :
    Configuration (FinLatticeField d N) :=
  { toFun := fun f => ∑ x : FinLatticeSites d N, f x * φ x
    map_add' := fun f g => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' := fun r f => by
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]
    cont := continuous_finset_sum _ (fun i _ =>
      (continuous_apply i).mul continuous_const) }

/-- Lifting preserves delta function evaluation: `(liftToConfig φ)(δ_x) = φ(x)`. -/
private lemma liftToConfig_delta (φ : FinLatticeField d N) (x : FinLatticeSites d N) :
    (liftToConfig d N φ) (finLatticeDelta d N x) = φ x := by
  show ∑ z : FinLatticeSites d N, (finLatticeDelta d N x) z * φ z = φ x
  simp only [finLatticeDelta, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Any configuration equals the lift of its field values. -/
private lemma config_eq_liftToConfig (ω : Configuration (FinLatticeField d N)) :
    ω = liftToConfig d N (fun x => ω (finLatticeDelta d N x)) := by
  apply ContinuousLinearMap.ext; intro f
  show ω f = ∑ z : FinLatticeSites d N, f z * ω (finLatticeDelta d N z)
  conv_lhs => rw [show f = ∑ y : FinLatticeSites d N, f y • finLatticeDelta d N y from
    field_basis_decomposition d N f]
  simp only [map_sum, map_smul, smul_eq_mul]

/-- `IsFieldMonotone` implies `Monotone` for the lifted function. -/
private lemma isFieldMonotone_lift {F : Configuration (FinLatticeField d N) → ℝ}
    (hF : IsFieldMonotone d N F) :
    Monotone (fun φ : FinLatticeField d N => F (liftToConfig d N φ)) := by
  intro φ₁ φ₂ hle
  apply hF
  intro x
  simp only [liftToConfig_delta]
  exact hle x

/-! ### Gaussian density and FKG lattice condition

The lattice Gaussian measure has precision matrix Q = -Δ_a + m².
We define the Gaussian density explicitly and show it satisfies the FKG
lattice condition by the chain: non-positive off-diagonals → submodularity
→ FKG lattice condition. -/

-- gaussianDensity and massOperatorEntry are now defined in SpectralCovariance.lean

/-- The mass operator has non-positive off-diagonal entries.
The `m²` term is diagonal, and `-Δ` has off-diagonal entries `-a⁻²` for
neighbors and `0` otherwise — all ≤ 0.

Proof: For x ≠ y, δ_y(x) = 0 so the mass term m²·δ_y(x) vanishes.
The Laplacian term -(Δδ_y)(x) = -a⁻²·Σᵢ[δ_y(x+eᵢ) + δ_y(x-eᵢ)] ≤ 0
since each delta value is 0 or 1 and a⁻² ≥ 0. -/
theorem massOperator_offDiag_nonpos (d N : ℕ) [NeZero N] (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    ∀ x y : FinLatticeSites d N, x ≠ y → massOperatorEntry d N a mass x y ≤ 0 := by
  intro x y hxy
  -- Unfold mass operator entry to CLM operations
  simp only [massOperatorEntry, massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  -- The delta function at y evaluates to 0 at x ≠ y
  have hδ : finLatticeDelta d N y x = 0 := by
    simp only [finLatticeDelta, if_neg hxy]
  rw [hδ, mul_zero, add_zero]
  -- Goal: -(finiteLaplacian d N a (δ_y) x) ≤ 0, i.e., the Laplacian value is ≥ 0
  apply neg_nonpos_of_nonneg
  -- Unfold to finiteLaplacianFun
  show 0 ≤ finiteLaplacianFun d N a (finLatticeDelta d N y) x
  simp only [finiteLaplacianFun, finLatticeDelta, if_neg hxy, mul_zero, sub_zero]
  -- Goal: 0 ≤ a⁻¹² · Σᵢ (ite + ite) — each ite is 0 or 1
  apply mul_nonneg (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i _
  apply add_nonneg <;> (split_ifs <;> norm_num)

/-- The mass operator applied to φ, evaluated at x, equals the sum over
matrix entries times field values. -/
private lemma massOperator_apply_eq_sum (a mass : ℝ) (φ : FinLatticeField d N)
    (x : FinLatticeSites d N) :
    (massOperator d N a mass φ) x =
    ∑ y : FinLatticeSites d N, massOperatorEntry d N a mass x y * φ y := by
  conv_lhs => rw [field_basis_decomposition d N φ]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    massOperatorEntry]
  congr 1; ext y; ring

/-- The quadratic form `⟨φ, Qφ⟩` equals the double sum of matrix entries. -/
private lemma massOperator_bilinear_eq_sum (a mass : ℝ) (φ : FinLatticeField d N) :
    ∑ x, φ x * (massOperator d N a mass φ) x =
    ∑ x, ∑ y, massOperatorEntry d N a mass x y * φ x * φ y := by
  congr 1; ext x
  rw [massOperator_apply_eq_sum d N a mass φ x, Finset.mul_sum]
  congr 1; ext y; ring

/-- The Gaussian density satisfies the FKG lattice condition.

Proof chain:
1. The mass operator Q has non-positive off-diagonal entries (`massOperator_offDiag_nonpos`)
2. The quadratic form ½⟨φ,Qφ⟩ is submodular (`quadraticForm_submodular_of_nonpos_offDiag`)
3. exp(-submodular) satisfies the FKG lattice condition (`fkg_lattice_condition_of_submodular`) -/
theorem gaussianDensity_fkg_lattice_condition (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    FKGLatticeCondition (gaussianDensity d N a mass) := by
  intro x y
  unfold gaussianDensity
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp_of_le
  -- Rewrite quadratic forms as double sums
  have hQ := massOperator_offDiag_nonpos d N a mass ha hmass
  have hsub := quadraticForm_submodular_of_nonpos_offDiag
    (massOperatorEntry d N a mass) hQ x y
  simp only [massOperator_bilinear_eq_sum d N] at *
  linarith

-- gaussianDensity_nonneg is now in SpectralCovariance.lean

/-! ### Density bridge (proved)

The density bridge connects the abstract `latticeGaussianMeasure` (constructed
via pushforward of noise measure) with the explicit Gaussian density. It states
that expectations over the Gaussian measure can be computed as weighted Lebesgue
integrals with the Gaussian density.

Proved in `GaussianField.Density` via characteristic function matching:
both measures have charFun `exp(-½ ⟨t, Q⁻¹t⟩)`, so they are equal. -/

-- Re-export from GaussianField.Density (no longer an axiom)
#check @GaussianField.latticeGaussianMeasure_density_integral

/-- The Gaussian density is integrable against Lebesgue measure on `ℝ^{N^d}`.

Proof: The mass operator Q = -Δ + m² satisfies ⟨φ,Qφ⟩ ≥ m²‖φ‖² (since -Δ is
positive semidefinite). So exp(-½⟨φ,Qφ⟩) ≤ Π_x exp(-m²/2 · φ(x)²), which is
a product of integrable 1D Gaussians. -/
theorem gaussianDensity_integrable (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (gaussianDensity d N a mass) := by
  -- Step 1: Bilinear form lower bound: ⟨φ,Qφ⟩ ≥ m²‖φ‖²
  have hQ_bound : ∀ φ : FinLatticeField d N,
      mass ^ 2 * ∑ x, φ x ^ 2 ≤ ∑ x, φ x * (massOperator d N a mass φ) x := by
    intro φ
    simp only [massOperator, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    have split : ∀ x : FinLatticeSites d N,
        φ x * (-(finiteLaplacian d N a φ) x + mass ^ 2 * φ x) =
        -(φ x * (finiteLaplacian d N a φ) x) + mass ^ 2 * φ x ^ 2 := by
      intro x; ring
    simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
    linarith [finiteLaplacian_neg_semidefinite d N a ha φ]
  -- Step 2: Pointwise bound: gaussianDensity ≤ product of 1D Gaussians
  set b := mass ^ 2 / 2 with hb_def
  have hb_pos : 0 < b := by positivity
  have hpw : ∀ φ : FinLatticeField d N,
      gaussianDensity d N a mass φ ≤
      ∏ x : FinLatticeSites d N, Real.exp (-b * φ x ^ 2) := by
    intro φ
    simp only [gaussianDensity]
    rw [show ∏ x : FinLatticeSites d N, Real.exp (-b * φ x ^ 2) =
        Real.exp (∑ x, -b * φ x ^ 2) from
      (Real.exp_sum Finset.univ _).symm]
    apply Real.exp_le_exp_of_le
    rw [show ∑ x : FinLatticeSites d N, -b * φ x ^ 2 =
        -(1/2) * (mass ^ 2 * ∑ x, φ x ^ 2) from by
      simp only [hb_def, Finset.mul_sum]; ring_nf]
    exact mul_le_mul_of_nonpos_left (hQ_bound φ) (by norm_num)
  -- Step 3: Product of 1D Gaussians is integrable
  have h1d : ∀ _ : FinLatticeSites d N,
      Integrable (fun t : ℝ => Real.exp (-b * t ^ 2)) volume :=
    fun _ => integrable_exp_neg_mul_sq hb_pos
  have hprod : Integrable
      (fun φ : FinLatticeField d N =>
        ∏ x : FinLatticeSites d N, Real.exp (-b * φ x ^ 2)) := by
    exact Integrable.fintype_prod h1d
  -- Step 4: Dominated by integrable function
  exact hprod.mono
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finset_sum _ fun x _ =>
        (continuous_apply x).mul
          ((continuous_apply x).comp (massOperator d N a mass).continuous)))).aestronglyMeasurable
    (ae_of_all _ fun φ => by
      rw [Real.norm_of_nonneg (gaussianDensity_nonneg d N a mass φ),
          Real.norm_of_nonneg (Finset.prod_nonneg fun x _ => le_of_lt (Real.exp_pos _))]
      exact hpw φ)

/-- The Gaussian integral is strictly positive: `∫ exp(-½⟨φ,Qφ⟩) dφ > 0`.
Follows from: gaussianDensity is continuous, everywhere positive, and integrable.
Uses `integral_pos_of_integrable_nonneg_nonzero` with `IsOpenPosMeasure volume`. -/
theorem gaussianDensity_integral_pos (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < ∫ φ, gaussianDensity d N a mass φ := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · -- Continuous: exp ∘ (const * finite sum of continuous terms)
    unfold gaussianDensity
    exact Real.continuous_exp.comp (continuous_const.mul
      (continuous_finset_sum _ fun x _ =>
        (continuous_apply x).mul
          ((continuous_apply x).comp (massOperator d N a mass).continuous)))
  · exact gaussianDensity_integrable d N a mass ha hmass
  · exact fun φ => le_of_lt (Real.exp_pos _)
  · exact ne_of_gt (Real.exp_pos _)

-- Re-export from GaussianField.Density (no longer an axiom)
#check @GaussianField.integrable_mul_gaussianDensity

/-! ### FKG for the Gaussian measure

With the density bridge and the proved FKG lattice condition for the Gaussian
density, we derive the FKG inequality for the lattice Gaussian measure. -/

/-- **FKG inequality for the lattice Gaussian measure.**

For FKG-monotone functions F, G on Configuration space,
the Gaussian measure satisfies `E_μ[F · G] ≥ E_μ[F] · E_μ[G]`.

Proof: Rewrite integrals using the density bridge, then apply
`fkg_from_lattice_condition` with the Gaussian density. -/
theorem gaussian_fkg_lattice_condition (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable F (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable G (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (F * G) (latticeGaussianMeasure d N a mass ha hmass)) :
    (∫ ω, F ω * G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) ≥
    (∫ ω, F ω ∂(latticeGaussianMeasure d N a mass ha hmass)) *
    (∫ ω, G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) := by
  -- Abbreviations for readability
  set F' := fun φ : FinLatticeField d N => F (liftToConfig d N φ) with hF'_def
  set G' := fun φ : FinLatticeField d N => G (liftToConfig d N φ) with hG'_def
  set ρ := gaussianDensity d N a mass with hρ_def
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ_def
  -- Step 1: Rewrite F(ω) = F'(field values of ω) using config_eq_liftToConfig
  have hF_eq : ∀ ω, F ω = F' (fun x => ω (finLatticeDelta d N x)) :=
    fun ω => congr_arg F (config_eq_liftToConfig d N ω)
  have hG_eq : ∀ ω, G ω = G' (fun x => ω (finLatticeDelta d N x)) :=
    fun ω => congr_arg G (config_eq_liftToConfig d N ω)
  -- Step 2: Integrability of weighted functions (Lebesgue measure on ℝ^{N^d})
  -- Transfer integrability from Gaussian measure to Lebesgue via density bridge
  have hF'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        F' (fun x => ω (finLatticeDelta d N x))) μ :=
    hFi.congr (by filter_upwards with ω; exact hF_eq ω)
  have hG'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        G' (fun x => ω (finLatticeDelta d N x))) μ :=
    hGi.congr (by filter_upwards with ω; exact hG_eq ω)
  have hFG'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        (fun φ => F' φ * G' φ) (fun x => ω (finLatticeDelta d N x))) μ :=
    hFGi.congr (by filter_upwards with ω; simp only [Pi.mul_apply, hF_eq, hG_eq])
  have hF'ρi : Integrable (fun φ => F' φ * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass F' hF'_int
  have hG'ρi : Integrable (fun φ => G' φ * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass G' hG'_int
  have hFG'ρi : Integrable (fun φ => F' φ * G' φ * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass
      (fun φ => F' φ * G' φ) hFG'_int
  -- Step 3: Rewrite each integral using density bridge
  have hI_FG : ∫ ω, F ω * G ω ∂μ = (∫ φ, F' φ * G' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω * G ω ∂μ) =
        ∫ ω, (fun φ => F' φ * G' φ) (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hF_eq, hG_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _ hFG'ρi
  have hI_F : ∫ ω, F ω ∂μ = (∫ φ, F' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω ∂μ) =
        ∫ ω, F' (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; exact hF_eq ω)]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass F' hF'ρi
  have hI_G : ∫ ω, G ω ∂μ = (∫ φ, G' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, G ω ∂μ) =
        ∫ ω, G' (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; exact hG_eq ω)]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass G' hG'ρi
  -- Step 4: Apply FKG in unnormalized form, then convert to normalized
  have hρ_pos : 0 < ∫ φ, ρ φ := gaussianDensity_integral_pos d N a mass ha hmass
  have hfkg := fkg_from_lattice_condition ρ (gaussianDensity_nonneg d N a mass)
    (gaussianDensity_fkg_lattice_condition d N a mass ha hmass) F' G'
    (isFieldMonotone_lift d N hF) (isFieldMonotone_lift d N hG)
    (gaussianDensity_integrable d N a mass ha hmass) hF'ρi hG'ρi hFG'ρi
  -- Convert: (∫ F'G'ρ)(∫ ρ) ≥ (∫ F'ρ)(∫ G'ρ) implies (∫ F'G'ρ)/(∫ ρ) ≥ (∫ F'ρ/∫ρ)·(∫ G'ρ/∫ρ)
  rw [hI_FG, hI_F, hI_G, ge_iff_le, div_mul_div_comm]
  exact (div_le_div_iff₀ (mul_pos hρ_pos hρ_pos) hρ_pos).mpr (by nlinarith [hfkg])

/-- Synonym for `gaussian_fkg_lattice_condition`. -/
theorem fkg_lattice_gaussian (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable F (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable G (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (F * G) (latticeGaussianMeasure d N a mass ha hmass)) :
    (∫ ω, F ω * G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) ≥
    (∫ ω, F ω ∂(latticeGaussianMeasure d N a mass ha hmass)) *
    (∫ ω, G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) :=
  gaussian_fkg_lattice_condition d N a mass ha hmass F G hF hG hFi hGi hFGi

/-! ### FKG for perturbed measures -/

/-- **FKG inequality for the perturbed (interacting) measure.**

If V : Configuration → ℝ is a sum of single-site functions, then the perturbed
measure `dμ_V = (1/Z) exp(-V) dμ₀` also satisfies FKG for FKG-monotone F, G.

This covers P(φ)₂ field theory. Global convexity of V is NOT needed.

Proof: The Gaussian density ρ₀ satisfies the FKG lattice condition
(proved: `gaussianDensity_fkg_lattice_condition`). The weight exp(-V) satisfies
it when V is single-site (proved: `fkg_lattice_condition_single_site`).
Their product satisfies it (proved: `fkg_lattice_condition_mul`).
Apply `fkg_from_lattice_condition` to the product density. -/
theorem fkg_perturbed (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (V : Configuration (FinLatticeField d N) → ℝ)
    (hV_single_site : ∃ v : FinLatticeSites d N → (ℝ → ℝ),
      ∀ ω : Configuration (FinLatticeField d N),
        V ω = ∑ x, v x (ω (finLatticeDelta d N x)))
    (hV_integrable : Integrable (fun ω => Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable (fun ω => F ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable (fun ω => G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (fun ω => F ω * G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass)) :
    let μ := latticeGaussianMeasure d N a mass ha hmass
    (∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ) * (∫ ω, Real.exp (-V ω) ∂μ) ≥
    (∫ ω, F ω * Real.exp (-V ω) ∂μ) * (∫ ω, G ω * Real.exp (-V ω) ∂μ) := by
  intro μ
  -- Lift to FinLatticeField
  set F' := fun φ : FinLatticeField d N => F (liftToConfig d N φ) with hF'_def
  set G' := fun φ : FinLatticeField d N => G (liftToConfig d N φ) with hG'_def
  set V' := fun φ : FinLatticeField d N => V (liftToConfig d N φ) with hV'_def
  set ρ := gaussianDensity d N a mass with hρ_def
  -- V' is single-site (transfer from hV_single_site via liftToConfig)
  obtain ⟨v, hv⟩ := hV_single_site
  have hV'_single : IsSingleSite V' := by
    exact ⟨v, fun φ => by
      show V (liftToConfig d N φ) = ∑ x, v x (φ x)
      rw [hv]; congr 1; ext x; congr 1; exact liftToConfig_delta d N φ x⟩
  -- Combined density ρ' = ρ · exp(-V') satisfies FKG lattice condition
  set ρ' := fun φ => ρ φ * Real.exp (-V' φ) with hρ'_def
  have hρ'_fkg : FKGLatticeCondition ρ' :=
    fkg_lattice_condition_mul
      (gaussianDensity_fkg_lattice_condition d N a mass ha hmass)
      (fkg_lattice_condition_single_site V' hV'_single)
      (gaussianDensity_nonneg d N a mass)
      (fun φ => le_of_lt (Real.exp_pos _))
  have hρ'_nn : ∀ φ, 0 ≤ ρ' φ :=
    fun φ => mul_nonneg (gaussianDensity_nonneg d N a mass φ) (le_of_lt (Real.exp_pos _))
  -- Rewrite using config_eq_liftToConfig
  have hF_eq : ∀ ω, F ω = F' (fun x => ω (finLatticeDelta d N x)) :=
    fun ω => congr_arg F (config_eq_liftToConfig d N ω)
  have hG_eq : ∀ ω, G ω = G' (fun x => ω (finLatticeDelta d N x)) :=
    fun ω => congr_arg G (config_eq_liftToConfig d N ω)
  have hV_eq : ∀ ω, V ω = V' (fun x => ω (finLatticeDelta d N x)) :=
    fun ω => congr_arg V (config_eq_liftToConfig d N ω)
  -- Integrability of weighted functions (Lebesgue measure on ℝ^{N^d})
  -- All follow from density bridge + integrability on the Gaussian measure.
  -- Transfer integrability from Gaussian measure to Lebesgue via density bridge
  have hV'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        (fun φ => Real.exp (-V' φ)) (fun x => ω (finLatticeDelta d N x))) μ :=
    hV_integrable.congr (by filter_upwards with ω; simp only [hV_eq])
  have hFV'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        (fun φ => F' φ * Real.exp (-V' φ)) (fun x => ω (finLatticeDelta d N x))) μ :=
    hFi.congr (by filter_upwards with ω; simp only [hF_eq, hV_eq])
  have hGV'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        (fun φ => G' φ * Real.exp (-V' φ)) (fun x => ω (finLatticeDelta d N x))) μ :=
    hGi.congr (by filter_upwards with ω; simp only [hG_eq, hV_eq])
  have hFGV'_int : Integrable
      (fun ω : Configuration (FinLatticeField d N) =>
        (fun φ => F' φ * G' φ * Real.exp (-V' φ)) (fun x => ω (finLatticeDelta d N x))) μ :=
    hFGi.congr (by filter_upwards with ω; simp only [hF_eq, hG_eq, hV_eq])
  have hVρi : Integrable (fun φ => Real.exp (-V' φ) * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass _ hV'_int
  have hFVρi : Integrable (fun φ => F' φ * Real.exp (-V' φ) * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass _ hFV'_int
  have hGVρi : Integrable (fun φ => G' φ * Real.exp (-V' φ) * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass _ hGV'_int
  have hFGVρi : Integrable (fun φ => F' φ * G' φ * Real.exp (-V' φ) * ρ φ) :=
    integrable_mul_gaussianDensity d N a mass ha hmass _ hFGV'_int
  have hρ'i : Integrable ρ' :=
    hVρi.congr (ae_of_all _ (fun φ => by simp only [hρ'_def]; ring))
  have hFρ'i : Integrable (fun φ => F' φ * ρ' φ) :=
    hFVρi.congr (ae_of_all _ (fun φ => by simp only [hρ'_def]; ring))
  have hGρ'i : Integrable (fun φ => G' φ * ρ' φ) :=
    hGVρi.congr (ae_of_all _ (fun φ => by simp only [hρ'_def]; ring))
  have hFGρ'i : Integrable (fun φ => F' φ * G' φ * ρ' φ) :=
    hFGVρi.congr (ae_of_all _ (fun φ => by simp only [hρ'_def]; ring))
  -- Rewrite integrals using density bridge
  have hI_FGV : ∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ =
      (∫ φ, F' φ * G' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ) =
        ∫ ω, (fun φ => F' φ * G' φ * Real.exp (-V' φ))
          (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hF_eq, hG_eq, hV_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _ hFGVρi
  have hI_V : ∫ ω, Real.exp (-V ω) ∂μ =
      (∫ φ, Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, Real.exp (-V ω) ∂μ) =
        ∫ ω, (fun φ => Real.exp (-V' φ))
          (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hV_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _ hVρi
  have hI_FV : ∫ ω, F ω * Real.exp (-V ω) ∂μ =
      (∫ φ, F' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω * Real.exp (-V ω) ∂μ) =
        ∫ ω, (fun φ => F' φ * Real.exp (-V' φ))
          (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hF_eq, hV_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _ hFVρi
  have hI_GV : ∫ ω, G ω * Real.exp (-V ω) ∂μ =
      (∫ φ, G' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, G ω * Real.exp (-V ω) ∂μ) =
        ∫ ω, (fun φ => G' φ * Real.exp (-V' φ))
          (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hG_eq, hV_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _ hGVρi
  -- Apply FKG to combined density ρ'
  have hfkg := fkg_from_lattice_condition ρ' hρ'_nn hρ'_fkg F' G'
    (isFieldMonotone_lift d N hF) (isFieldMonotone_lift d N hG)
    hρ'i hFρ'i hGρ'i hFGρ'i
  -- hfkg: (∫ F'G'ρ')(∫ ρ') ≥ (∫ F'ρ')(∫ G'ρ')
  -- Equate integrals: ∫ F'ρ' = ∫ F'e^{-V'}ρ, etc.
  have hI_eq1 : ∫ φ, F' φ * G' φ * ρ' φ =
      ∫ φ, F' φ * G' φ * Real.exp (-V' φ) * ρ φ :=
    integral_congr_ae (by filter_upwards with φ; simp only [hρ'_def]; ring)
  have hI_eq2 : ∫ φ, ρ' φ = ∫ φ, Real.exp (-V' φ) * ρ φ :=
    integral_congr_ae (by filter_upwards with φ; simp only [hρ'_def]; ring)
  have hI_eq3 : ∫ φ, F' φ * ρ' φ = ∫ φ, F' φ * Real.exp (-V' φ) * ρ φ :=
    integral_congr_ae (by filter_upwards with φ; simp only [hρ'_def]; ring)
  have hI_eq4 : ∫ φ, G' φ * ρ' φ = ∫ φ, G' φ * Real.exp (-V' φ) * ρ φ :=
    integral_congr_ae (by filter_upwards with φ; simp only [hρ'_def]; ring)
  -- Substitute and simplify
  rw [hI_FGV, hI_V, hI_FV, hI_GV, ge_iff_le, div_mul_div_comm, div_mul_div_comm]
  have hρ_pos : 0 < ∫ φ, ρ φ := gaussianDensity_integral_pos d N a mass ha hmass
  exact (div_le_div_iff₀ (mul_pos hρ_pos hρ_pos) (mul_pos hρ_pos hρ_pos)).mpr
    (by rw [← hI_eq3, ← hI_eq4, ← hI_eq1, ← hI_eq2]; nlinarith [hfkg])

end GaussianField
