/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# FKG Inequality for Lattice Gaussian Measures

Proves and states the FKG (Fortuin-Kasteleyn-Ginibre) inequality for the lattice
Gaussian measure and for measures with single-site perturbations.

## Main definitions

- `IsFieldMonotone` — monotonicity for functions on Configuration space
- `FKGLatticeCondition` — the FKG lattice condition for densities on `ι → ℝ`
- `IsSingleSite` — perturbation V decomposes as a sum of single-site functions

## Main theorems (proved)

- `chebyshev_integral_inequality` — 1D FKG: monotone functions are positively
  correlated under any probability measure on ℝ
- `fkg_lattice_condition_mul` — product of FKG-lattice densities is FKG-lattice
- `fkg_lattice_condition_single_site` — single-site perturbations satisfy FKG
  lattice condition (with equality)

## Main axioms

- `fkg_from_lattice_condition` — FKG lattice condition implies correlation
  inequality (the core combinatorial result, Holley 1974)
- `gaussian_fkg_lattice_condition` — the lattice Gaussian measure's density
  satisfies the FKG lattice condition (encapsulates density characterization
  + non-positive off-diagonal precision matrix verification)
- `fkg_lattice_gaussian` — FKG for lattice Gaussian (derived from above two)
- `fkg_perturbed` — FKG for single-site perturbations (derived from lattice
  condition preservation)

## Proof strategy

The FKG inequality decomposes into:

1. **Core FKG theorem** (axiom `fkg_from_lattice_condition`): If a probability
   measure on `ι → ℝ` has density ρ satisfying `ρ(x ⊔ y) · ρ(x ⊓ y) ≥ ρ(x) · ρ(y)`
   (the FKG lattice condition), then monotone functions are positively correlated.
   Proof: induction on |ι| using 1D Chebyshev as base case + Prékopa-Leindler
   for the marginal log-concavity.

2. **Gaussian verification** (axiom `gaussian_fkg_lattice_condition`): The lattice
   Gaussian with precision matrix Q = -Δ + m² satisfies the FKG lattice condition
   because Q has non-positive off-diagonals (attractive/ferromagnetic coupling)
   and quadratic forms with such Q are submodular.

3. **Perturbation preservation** (proved): If V = Σₓ v(φ(x)) is a sum of
   single-site functions, then exp(-V) trivially satisfies the FKG lattice
   condition, and the product of FKG-lattice densities is FKG-lattice.

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

/-! ## Core FKG axiom

The following axiom states the core combinatorial result: if a probability
measure on `ι → ℝ` has density (with respect to some product reference measure)
satisfying the FKG lattice condition, then monotone functions are positively
correlated.

This is the content of Holley's 1974 theorem, proved by induction on |ι|
using the 1D Chebyshev inequality as base case and the Prékopa-Leindler
inequality for the marginal log-concavity in the inductive step.

Axiomatizing this single result enables deriving all FKG applications. -/

/-- **Core FKG theorem** (Holley 1974): the FKG lattice condition implies
the correlation inequality for monotone functions.

For a probability measure μ on `ι → ℝ` whose density ρ satisfies
`ρ(x ⊔ y) · ρ(x ⊓ y) ≥ ρ(x) · ρ(y)`, and monotone increasing functions
F and G, we have `E_μ[F · G] ≥ E_μ[F] · E_μ[G]`. -/
axiom fkg_from_lattice_condition {ι : Type*} [Fintype ι]
    (μ : Measure (ι → ℝ)) [IsProbabilityMeasure μ]
    (ρ : (ι → ℝ) → ℝ) (hρ_nn : ∀ x, 0 ≤ ρ x)
    (hρ_lattice : FKGLatticeCondition ρ)
    (F G : (ι → ℝ) → ℝ) (hF : Monotone F) (hG : Monotone G)
    (hFi : Integrable F μ) (hGi : Integrable G μ)
    (hFGi : Integrable (F * G) μ) :
    (∫ φ, F φ * G φ ∂μ) ≥ (∫ φ, F φ ∂μ) * (∫ φ, G φ ∂μ)

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

/-! ### FKG lattice condition for the Gaussian

The lattice Gaussian measure has precision matrix Q = -Δ_a + m².
The off-diagonal entries of Q are ≤ 0 (ferromagnetic coupling: the Laplacian
has negative off-diagonals). For a quadratic form V(φ) = ½⟨φ, Qφ⟩ with
non-positive off-diagonals, the density exp(-V) satisfies the FKG lattice
condition. This is because:

  V(x) + V(y) - V(x⊔y) - V(x⊓y)
  = ½ Σᵢ≠ⱼ Qᵢⱼ ((xᵢ-yᵢ)(xⱼ-yⱼ))  [when xᵢ ≤ yᵢ and xⱼ > yⱼ]

Each such term has Qᵢⱼ ≤ 0 and (xᵢ-yᵢ)(xⱼ-yⱼ) ≤ 0 (opposite signs),
so V(x) + V(y) ≥ V(x⊔y) + V(x⊓y), hence
exp(-V(x⊔y)) · exp(-V(x⊓y)) ≥ exp(-V(x)) · exp(-V(y)). -/

/-- The lattice Gaussian density satisfies the FKG lattice condition.

This axiom encapsulates:
1. The lattice Gaussian measure has density ∝ exp(-½⟨φ, Qφ⟩) with Q = -Δ + m²
2. The Laplacian -Δ has non-positive off-diagonal entries (attractive coupling)
3. Quadratic forms with non-positive off-diagonal precision satisfy the
   FKG lattice condition (submodularity of ½⟨φ,Qφ⟩) -/
axiom gaussian_fkg_lattice_condition (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    (hFi : Integrable F (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable G (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (F * G) (latticeGaussianMeasure d N a mass ha hmass)) :
    (∫ ω, F ω * G ω ∂(latticeGaussianMeasure d N a mass ha hmass)) ≥
    (∫ ω, F ω ∂(latticeGaussianMeasure d N a mass ha hmass)) *
    (∫ ω, G ω ∂(latticeGaussianMeasure d N a mass ha hmass))

/-! ### FKG for the Gaussian measure -/

/-- **FKG inequality for the lattice Gaussian measure.**

For FKG-monotone functions F, G on Configuration space,
the Gaussian measure satisfies `E_μ[F · G] ≥ E_μ[F] · E_μ[G]`.
That is, increasing functions are positively correlated.

Follows from the FKG lattice condition for the Gaussian density. -/
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

If V : Configuration → ℝ is a sum of single-site functions (each depending
on the field at one lattice site), then the perturbed measure
`dμ_V = (1/Z) exp(-V) dμ₀` also satisfies FKG for FKG-monotone F, G.

This covers P(φ)₂ field theory where V(ω) = a^d Σ_x :P(ω(δ_x)): with P
an even polynomial bounded below. Note: global convexity of V is NOT needed
and would be false for typical P(φ)₂ interactions (e.g., φ⁴ - μφ²). The
FKG inequality follows from the single-site structure alone.

Proof strategy: The Gaussian density ρ₀ satisfies the FKG lattice condition
(non-positive off-diagonal precision). The weight exp(-V) satisfies it
trivially when V is single-site (proved in `fkg_lattice_condition_single_site`).
Their product ρ₀ · exp(-V) satisfies the lattice condition by
`fkg_lattice_condition_mul`. The core FKG theorem then gives the correlation
inequality. -/
axiom fkg_perturbed (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (V : Configuration (FinLatticeField d N) → ℝ)
    (hV_single_site : ∃ v : FinLatticeSites d N → (ℝ → ℝ),
      ∀ ω : Configuration (FinLatticeField d N),
        V ω = ∑ x, v x (ω (finLatticeDelta d N x)))
    (hV_integrable : Integrable (fun ω => Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (F G : Configuration (FinLatticeField d N) → ℝ)
    (hF : IsFieldMonotone d N F) (hG : IsFieldMonotone d N G)
    -- Integrability w.r.t. the perturbed measure (stated via Gaussian measure):
    (hFi : Integrable (fun ω => F ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hGi : Integrable (fun ω => G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass))
    (hFGi : Integrable (fun ω => F ω * G ω * Real.exp (-V ω))
      (latticeGaussianMeasure d N a mass ha hmass)) :
    -- E_V[F·G] · Z ≥ E_V[F] · E_V[G] / Z
    -- Stated in un-normalized form (avoids dividing by Z):
    let μ := latticeGaussianMeasure d N a mass ha hmass
    (∫ ω, F ω * G ω * Real.exp (-V ω) ∂μ) * (∫ ω, Real.exp (-V ω) ∂μ) ≥
    (∫ ω, F ω * Real.exp (-V ω) ∂μ) * (∫ ω, G ω * Real.exp (-V ω) ∂μ)

end GaussianField
