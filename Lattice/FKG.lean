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
- `fkg_lattice_condition_mul` — product preserves FKG lattice condition
- `fkg_lattice_condition_single_site` — single-site exp(-V) satisfies FKG
- `fkg_lattice_condition_of_submodular` — exp(-V) satisfies FKG if V submodular
- `sup_inf_mul_add_le` — max-min product inequality (algebra)
- `quadraticForm_submodular_of_nonpos_offDiag` — quadratic forms with
  non-positive off-diagonal are submodular
- `gaussianDensity_fkg_lattice_condition` — Gaussian density satisfies FKG

## Axioms (3)

- `fkg_from_lattice_condition` — FKG lattice condition implies correlation
  inequality (Holley 1974); proof requires induction + Prékopa-Leindler
- `massOperator_offDiag_nonpos` — mass operator has non-positive off-diagonals;
  should be provable from `finiteLaplacianFun` definition
- `latticeGaussianMeasure_density_integral` — density bridge: Gaussian measure
  expectations = normalized weighted Lebesgue integrals

## Derived theorems (with sorry for measure-theory glue)

- `gaussian_fkg_lattice_condition` — FKG for Gaussian measure
- `fkg_perturbed` — FKG for single-site perturbations

## Proof architecture

```
massOperator_offDiag_nonpos → quadraticForm_submodular → gaussianDensity_fkg
                                                              ↓
  fkg_from_lattice_condition + density bridge → gaussian_fkg_lattice_condition
                                                              ↓
  + fkg_lattice_condition_single_site + fkg_lattice_condition_mul → fkg_perturbed
```

## References

- Fortuin, Kasteleyn, Ginibre (1971), "Correlation inequalities on some
  partially ordered sets"
- Holley (1974), "Remarks on the FKG inequalities"
- Glimm-Jaffe, "Quantum Physics", §19 (Correlation inequalities)
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", §IV
-/

import Lattice.Covariance
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

/-! ## Core FKG axiom

The core FKG theorem states that if a non-negative weight function ρ on
`ι → ℝ` satisfies the FKG lattice condition (log-supermodularity), then
monotone functions are positively correlated in the weighted integral:

  `(∫ F·G·ρ)(∫ ρ) ≥ (∫ F·ρ)(∫ G·ρ)`

This is the unnormalized form, avoiding division by the partition function.

Proof: induction on |ι| using the 1D Chebyshev inequality as base case
and marginal FKG-lattice preservation + Holley's criterion for the
inductive step.

References: Holley (1974), Preston (1974), Glimm-Jaffe §19. -/

/-- **Core FKG theorem** (Holley 1974): the FKG lattice condition implies
the correlation inequality for monotone functions.

Stated in unnormalized weighted integral form: for ρ satisfying
`ρ(x ⊔ y) · ρ(x ⊓ y) ≥ ρ(x) · ρ(y)` and monotone F, G,
`(∫ F·G·ρ)(∫ ρ) ≥ (∫ F·ρ)(∫ G·ρ)`. All integrals against Lebesgue measure. -/
axiom fkg_from_lattice_condition {ι : Type*} [Fintype ι]
    (ρ : (ι → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lattice : FKGLatticeCondition ρ)
    (F G : (ι → ℝ) → ℝ) (hF : Monotone F) (hG : Monotone G)
    (hρi : Integrable ρ)
    (hFρi : Integrable (fun φ => F φ * ρ φ))
    (hGρi : Integrable (fun φ => G φ * ρ φ))
    (hFGρi : Integrable (fun φ => F φ * G φ * ρ φ)) :
    (∫ φ, F φ * G φ * ρ φ) * (∫ φ, ρ φ) ≥
    (∫ φ, F φ * ρ φ) * (∫ φ, G φ * ρ φ)

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

/-- The Gaussian density on `FinLatticeField d N` (unnormalized):
`ρ(φ) = exp(-½ ⟨φ, Qφ⟩)` where Q = -Δ_a + m² is the mass operator. -/
def gaussianDensity (d N : ℕ) [NeZero N] (a mass : ℝ)
    (φ : FinLatticeField d N) : ℝ :=
  Real.exp (-(1/2) * ∑ x : FinLatticeSites d N,
    φ x * (massOperator d N a mass φ) x)

/-- The "matrix entries" of the mass operator: the bilinear form evaluated
on delta functions. `Q(x,y) = ⟨δ_x, (-Δ+m²)(δ_y)⟩`. -/
def massOperatorEntry (d N : ℕ) [NeZero N] (a mass : ℝ)
    (x y : FinLatticeSites d N) : ℝ :=
  (massOperator d N a mass (finLatticeDelta d N y)) x

/-- The mass operator has non-positive off-diagonal entries.
The `m²` term is diagonal, and `-Δ` has off-diagonal entries `-a⁻²` for
neighbors and `0` otherwise — all ≤ 0. -/
axiom massOperator_offDiag_nonpos (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    ∀ x y : FinLatticeSites d N, x ≠ y → massOperatorEntry d N a mass x y ≤ 0

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

/-- The Gaussian density is non-negative. -/
theorem gaussianDensity_nonneg (a mass : ℝ) (φ : FinLatticeField d N) :
    0 ≤ gaussianDensity d N a mass φ :=
  le_of_lt (Real.exp_pos _)

/-! ### Density bridge axiom

The following axiom bridges the abstract `latticeGaussianMeasure` (constructed
via pushforward of noise measure) with the explicit Gaussian density. It states
that expectations over the Gaussian measure can be computed as weighted Lebesgue
integrals with the Gaussian density.

This is the only axiom connecting abstract measure construction to concrete density.
All other FKG results follow from this + the proved algebraic lemmas. -/

/-- **Density bridge**: the lattice Gaussian measure equals a weighted
Lebesgue integral with the Gaussian density.

For any function F of field values, the expectation under the Gaussian measure
equals the normalized weighted integral:
`E_μ[F] = (∫ F(φ) · ρ(φ) dφ) / (∫ ρ(φ) dφ)`
where `ρ(φ) = exp(-½⟨φ, Qφ⟩)` and the integrals are against Lebesgue measure
on `FinLatticeField d N ≅ ℝ^{N^d}`.

This axiom encapsulates the connection between the pushforward construction
of the Gaussian measure and the classical density formula. -/
axiom latticeGaussianMeasure_density_integral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFρi : Integrable (fun φ => F φ * gaussianDensity d N a mass φ)) :
    ∫ ω, F (fun x => ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (∫ φ, F φ * gaussianDensity d N a mass φ) /
    (∫ φ, gaussianDensity d N a mass φ)

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
  -- Step 2: Rewrite each integral using density bridge
  have hI_FG : ∫ ω, F ω * G ω ∂μ = (∫ φ, F' φ * G' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω * G ω ∂μ) =
        ∫ ω, (fun φ => F' φ * G' φ) (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; simp only [hF_eq, hG_eq])]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass _
      (sorry : Integrable (fun φ => F' φ * G' φ * ρ φ))
  have hI_F : ∫ ω, F ω ∂μ = (∫ φ, F' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, F ω ∂μ) =
        ∫ ω, F' (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; exact hF_eq ω)]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass F'
      (sorry : Integrable (fun φ => F' φ * ρ φ))
  have hI_G : ∫ ω, G ω ∂μ = (∫ φ, G' φ * ρ φ) / (∫ φ, ρ φ) := by
    rw [show (∫ ω, G ω ∂μ) =
        ∫ ω, G' (fun x => ω (finLatticeDelta d N x)) ∂μ from
      integral_congr_ae (by filter_upwards with ω; exact hG_eq ω)]
    exact latticeGaussianMeasure_density_integral d N a mass ha hmass G'
      (sorry : Integrable (fun φ => G' φ * ρ φ))
  -- Step 3: Apply FKG in unnormalized form, then convert to normalized
  have hρ_pos : 0 < ∫ φ, ρ φ :=
    sorry -- Gaussian integral is strictly positive (ρ = exp(-½⟨φ,Qφ⟩) > 0)
  have hfkg := fkg_from_lattice_condition ρ (gaussianDensity_nonneg d N a mass)
    (gaussianDensity_fkg_lattice_condition d N a mass ha hmass) F' G'
    (isFieldMonotone_lift d N hF) (isFieldMonotone_lift d N hG)
    (sorry : Integrable ρ)
    (sorry : Integrable (fun φ => F' φ * ρ φ))
    (sorry : Integrable (fun φ => G' φ * ρ φ))
    (sorry : Integrable (fun φ => F' φ * G' φ * ρ φ))
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
  -- Rewrite each integral using density bridge
  -- Rewrite integrals using density bridge (sorry for integrability transfer)
  have hI_FGV : ∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ =
      (∫ φ, F' φ * G' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) :=
    sorry -- density bridge for F·G·exp(-V)
  have hI_V : ∫ ω, Real.exp (-V ω) ∂μ =
      (∫ φ, Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) :=
    sorry -- density bridge for exp(-V)
  have hI_FV : ∫ ω, F ω * Real.exp (-V ω) ∂μ =
      (∫ φ, F' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) :=
    sorry -- density bridge for F·exp(-V)
  have hI_GV : ∫ ω, G ω * Real.exp (-V ω) ∂μ =
      (∫ φ, G' φ * Real.exp (-V' φ) * ρ φ) / (∫ φ, ρ φ) :=
    sorry -- density bridge for G·exp(-V)
  -- Apply FKG to combined density ρ'
  have hfkg := fkg_from_lattice_condition ρ' hρ'_nn hρ'_fkg F' G'
    (isFieldMonotone_lift d N hF) (isFieldMonotone_lift d N hG)
    (sorry : Integrable ρ')
    (sorry : Integrable (fun φ => F' φ * ρ' φ))
    (sorry : Integrable (fun φ => G' φ * ρ' φ))
    (sorry : Integrable (fun φ => F' φ * G' φ * ρ' φ))
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
  have hρ_pos : 0 < ∫ φ, ρ φ :=
    sorry -- Gaussian integral is strictly positive
  exact (div_le_div_iff₀ (mul_pos hρ_pos hρ_pos) (mul_pos hρ_pos hρ_pos)).mpr
    (by rw [← hI_eq3, ← hI_eq4, ← hI_eq1, ← hI_eq2]; nlinarith [hfkg])

end GaussianField
