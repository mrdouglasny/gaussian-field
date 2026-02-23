/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick's Theorem (Isserlis' Theorem) for Gaussian Measures

Wick's theorem expresses the n-point functions of a centered Gaussian measure
in terms of the 2-point function (covariance). For the Gaussian measure
constructed in `GaussianField.Construction`:

- **Odd moments vanish**: E[ω(f₁)···ω(f₂ₖ₊₁)] = 0
- **Even moments factor into pairings**:
  E[ω(f₁)···ω(f₂ₖ)] = ∑_{pairings} ∏ C(fᵢ,fⱼ)

We state this in two forms:

1. **Recursive** (`wick_recursive`): Pick a partner for f₀ and recurse.
   This is the natural induction form and avoids enumerating pairings.

2. **Bound** (`wick_bound`): |E[∏ ω(fᵢ)]| ≤ (n-1)‼ · ∏ ‖T(fᵢ)‖.
   This is sufficient for verifying OS1' (Schwinger function growth).

## Proof strategy

The key tool is **Gaussian integration by parts**:
  E[ω(f₀) · F(ω)] = ∑ⱼ C(f₀, gⱼ) · E[∂F/∂(ω gⱼ)]
For F(ω) = ∏ᵢ ω(gᵢ), the derivative ∂F/∂(ω gⱼ) = ∏_{i≠j} ω(gᵢ).
This gives the recursive formula directly.

Gaussian IBP itself follows from differentiating the characteristic
functional `charFun T f` (proved in `GaussianField.Construction`):
  d/dt E[exp(it·ω(f))] |_{t=0} = i · E[ω(f)] = -⟨Tf, Tf⟩ · 0 = 0

## References

- Janson, "Gaussian Hilbert Spaces", Theorem 1.28
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", §I.3
- Glimm-Jaffe, "Quantum Physics", §6.1 (Wick ordering)
-/

import GaussianField.Properties
import Mathlib.Data.Nat.Factorial.DoubleFactorial

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-! ## Integrability of products

Products of n evaluation functionals are integrable, generalizing
`pairing_product_integrable` from n=2. This is needed for Wick's theorem
to be well-stated (the integrals must exist). -/

/-- HolderTriple (2p, 2p, p): `(2p)⁻¹ + (2p)⁻¹ = p⁻¹` in ℝ≥0∞.

This allows Hölder's inequality to be applied as: L^{2p} × L^{2p} → L^p. -/
private lemma holderTriple_double (p : ℝ≥0∞) :
    ENNReal.HolderTriple (2 * p) (2 * p) p where
  inv_add_inv_eq_inv := by
    have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
    have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc (2 * p)⁻¹ + (2 * p)⁻¹
        = 2 * (2 * p)⁻¹ := (two_mul _).symm
      _ = 2 * (2⁻¹ * p⁻¹) := by
          congr 1
          exact ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)
      _ = (2 * 2⁻¹) * p⁻¹ := by rw [mul_assoc]
      _ = 1 * p⁻¹ := by rw [ENNReal.mul_inv_cancel h2_ne_zero h2_ne_top]
      _ = p⁻¹ := one_mul _

/-- Products of evaluation functionals are in L^p for all p.

By induction on n, splitting ∏ = head × tail. At each step, `pairing_memLp`
gives head ∈ L^{2p}, and the IH gives tail ∈ L^{2p}. Hölder's inequality
via `HolderTriple (2p) (2p) p` gives the product ∈ L^p. -/
private theorem product_memLp : ∀ (n : ℕ) (f : Fin n → E) (p : ℝ≥0),
    MemLp (fun ω : Configuration E => ∏ i, ω (f i)) (↑p) (measure T) := by
  intro n
  induction n with
  | zero => intro f p; simp; exact memLp_const 1
  | succ n ih =>
    intro f p
    simp_rw [Fin.prod_univ_succ]
    haveI : ENNReal.HolderTriple (↑(2 * p)) (↑(2 * p)) (↑p) := by
      rw [ENNReal.coe_mul]; exact holderTriple_double ↑p
    have hf0 : MemLp (fun ω : Configuration E => ω (f 0)) (↑(2 * p)) (measure T) :=
      pairing_memLp T (f 0) (2 * p)
    have htail : MemLp (fun ω : Configuration E => ∏ i : Fin n, ω (f (Fin.succ i)))
        (↑(2 * p)) (measure T) :=
      ih (fun i => f (Fin.succ i)) (2 * p)
    exact htail.mul' hf0

/-- Finite products of evaluation functionals are integrable.

Corollary of `product_memLp` with p = 1. -/
theorem product_integrable (n : ℕ) (f : Fin n → E) :
    Integrable (fun ω : Configuration E => ∏ i, ω (f i)) (measure T) := by
  rw [← memLp_one_iff_integrable]
  exact_mod_cast product_memLp T n f 1

/-! ## Gaussian integration by parts

The key analytic input for Wick's theorem. This follows from differentiating
the characteristic functional `charFun T (t • f₀ + h)` at `t = 0` in two ways:

**Integral form** (Leibniz rule `hasDerivAt_integral_of_dominated_loc_of_deriv_le`):
  d/dt ∫ exp(i·ω(t·f₀+h)) dμ |_{t=0} = i · ∫ ω(f₀)·exp(i·ω(h)) dμ

**Closed form** (chain rule on `exp(-½‖T(t·f₀+h)‖²)`):
  d/dt exp(-½(t²‖Tf₀‖² + 2t⟨Tf₀,Th⟩ + ‖Th‖²)) |_{t=0} = -⟨Tf₀,Th⟩ · charFun T h

Equating gives: ∫ ω(f₀)·exp(i·ω(h)) dμ = ⟨Tf₀,Th⟩ · i · charFun T h

The domination condition for Leibniz: |d/dt exp(i·ω(t·f₀+h))| = |ω(f₀)| ∈ L¹
by `pairing_integrable`. -/

/-- Closed-form derivative of `charFun T (t • f₀ + h)` at `t = 0`.

Uses chain rule: `d/dt exp(-½⟨T(t•f₀+h), T(t•f₀+h)⟩)|_{t=0} = -⟨Tf₀,Th⟩ · charFun T h`. -/
private lemma hasDerivAt_charFun_closed (f₀ h : E) :
    HasDerivAt
      (fun t : ℝ => ∫ ω : Configuration E,
        Complex.exp (Complex.I * ↑(ω (t • f₀ + h))) ∂(measure T))
      ((-↑(@inner ℝ H _ (T f₀) (T h))) *
        ∫ ω : Configuration E,
          Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
      (0 : ℝ) := by
  -- Rewrite using charFun: ∫ exp(I·ω(f)) dμ = exp(-½⟨Tf,Tf⟩) for all f
  have hchar : ∀ t : ℝ,
      ∫ ω : Configuration E,
        Complex.exp (Complex.I * ↑(ω (t • f₀ + h))) ∂(measure T) =
      Complex.exp (-(1/2 : ℂ) * ↑(@inner ℝ H _ (T (t • f₀ + h)) (T (t • f₀ + h)))) :=
    fun t => charFun T (t • f₀ + h)
  simp_rw [hchar]
  -- T(t•f₀+h) = t•Tf₀ + Th by CLM linearity
  have hT : ∀ t : ℝ, T (t • f₀ + h) = t • T f₀ + T h := by
    intro t; simp [map_add, map_smul]
  simp_rw [hT]
  -- HasDerivAt for t ↦ t • Tf₀ + Th
  have hu : HasDerivAt (fun t : ℝ => t • T f₀ + T h) (T f₀) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (T f₀)).add_const (T h)
    simpa using this
  -- HasDerivAt for ⟨u(t), u(t)⟩: derivative = ⟨Th, Tf₀⟩ + ⟨Tf₀, Th⟩ at t=0
  have hq := HasDerivAt.inner (𝕜 := ℝ) hu hu
  -- Lift to ℂ and multiply by -½
  have hg := (hq.ofReal_comp).const_mul (-(1/2 : ℂ))
  -- Chain rule: exp(g(t))
  have hexp := hg.cexp
  convert hexp using 1
  -- Goal: -↑⟨Tf₀,Th⟩ * ∫ exp(I*ω(h)) dμ = exp(-½⟨Th,Th⟩) * (-½ * ↑(⟨Th,Tf₀⟩+⟨Tf₀,Th⟩))
  simp only [zero_smul, zero_add]
  rw [real_inner_comm (T h) (T f₀), charFun T h]
  push_cast; ring

/-- Leibniz derivative of `∫ exp(I·ω(t•f₀+h)) dμ` at `t = 0`.

Uses `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with domination by `|ω(f₀)|`. -/
private lemma charFun_integrand_measurable (f : E) :
    AEStronglyMeasurable
      (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω f)))
      (measure T) :=
  (((continuous_const.mul Complex.continuous_ofReal).cexp.measurable).comp
    (configuration_eval_measurable f)).aestronglyMeasurable

private lemma charFun_integrand_integrable (f : E) :
    Integrable
      (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω f)))
      (measure T) :=
  Integrable.of_bound (charFun_integrand_measurable T f) 1
    (.of_forall fun ω => by
      rw [Complex.norm_exp_I_mul_ofReal])

private lemma hasDerivAt_charFun_leibniz (f₀ h : E) :
    HasDerivAt
      (fun t : ℝ => ∫ ω : Configuration E,
        Complex.exp (Complex.I * ↑(ω (t • f₀ + h))) ∂(measure T))
      (∫ ω : Configuration E,
        Complex.I * ↑(ω f₀) * Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
      (0 : ℝ) := by
  -- Apply Leibniz integral rule
  have hleibniz := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (ω : Configuration E) => Complex.exp (Complex.I * ↑(ω (t • f₀ + h))))
    (F' := fun (t : ℝ) (ω : Configuration E) =>
      Complex.I * ↑(ω f₀) * Complex.exp (Complex.I * ↑(ω (t • f₀ + h))))
    (x₀ := (0 : ℝ)) (bound := fun ω => ‖ω f₀‖) (s := Set.univ)
    -- (1) s ∈ 𝓝 0
    Filter.univ_mem
    -- (2) F t is a.e. strongly measurable for t near 0
    (.of_forall fun t => charFun_integrand_measurable T (t • f₀ + h))
    -- (3) F 0 is integrable
    (by simpa using charFun_integrand_integrable T h)
    -- (4) F' 0 is a.e. strongly measurable
    (by
      have hmeas_eval : AEStronglyMeasurable (fun ω : Configuration E => (ω f₀ : ℂ))
          (measure T) :=
        (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable f₀)).aestronglyMeasurable
      have hmeas_exp : AEStronglyMeasurable
          (fun ω : Configuration E => Complex.exp (Complex.I * ↑(ω h)))
          (measure T) :=
        charFun_integrand_measurable T h
      simpa using (hmeas_eval.const_mul Complex.I).mul hmeas_exp)
    -- (5) ‖F' t ω‖ ≤ bound ω for all t ∈ s
    (.of_forall fun ω => by
      intro t _
      simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_exp_I_mul_ofReal,
        Complex.norm_real, one_mul, mul_one, le_refl])
    -- (6) bound is integrable
    ((pairing_integrable T f₀).norm)
    -- (7) ∀ᵐ ω, ∀ t ∈ s, HasDerivAt (F · ω) (F' t ω) t
    (.of_forall fun ω => by
      intro t _
      -- ω(t • f₀ + h) = t * ω(f₀) + ω(h) by CLM linearity
      have hlin : ∀ t', ω (t' • f₀ + h) = t' * ω f₀ + ω h := by
        intro t'; simp [map_add, map_smul]
      simp_rw [hlin]
      -- d/dt exp(I * ↑(t * a + b)) = I * ↑a * exp(I * ↑(t * a + b))
      have hg : HasDerivAt (fun t' => t' * ω f₀ + ω h) (ω f₀) t := by
        simpa using ((hasDerivAt_id t).mul_const (ω f₀)).add_const (ω h)
      have hc : HasDerivAt (fun t' => Complex.I * ↑(t' * ω f₀ + ω h))
          (Complex.I * ↑(ω f₀)) t :=
        (HasDerivAt.ofReal_comp hg).const_mul Complex.I
      -- cexp gives: exp(f(t)) * f'(t), we need f'(t) * exp(f(t))
      have hexp := hc.cexp
      rwa [mul_comm] at hexp)
  -- Extract the HasDerivAt from the conjunction and simplify at t=0
  convert hleibniz.2 using 2
  ext ω; simp

theorem gaussian_ibp (f₀ h : E) :
    ∫ ω : Configuration E,
      ↑(ω f₀) * Complex.exp (Complex.I * ↑(ω h)) ∂(measure T) =
    ↑(@inner ℝ H _ (T f₀) (T h)) * Complex.I *
      ∫ ω : Configuration E,
        Complex.exp (Complex.I * ↑(ω h)) ∂(measure T) := by
  -- Equate the two HasDerivAt results by uniqueness
  have hclosed := hasDerivAt_charFun_closed T f₀ h
  have hleibniz := hasDerivAt_charFun_leibniz T f₀ h
  have heq := hleibniz.unique hclosed
  -- heq : ∫ I * ↑(ω f₀) * exp(I * ↑(ω h)) dμ = (-↑b) * ∫ exp(I * ↑(ω h)) dμ
  -- Rewrite integrand as I * (rest)
  have hpull : ∀ ω : Configuration E,
      Complex.I * ↑(ω f₀) * Complex.exp (Complex.I * ↑(ω h)) =
      Complex.I * (↑(ω f₀) * Complex.exp (Complex.I * ↑(ω h))) := by
    intro ω; ring
  simp_rw [hpull] at heq
  -- Pull I out of the integral
  rw [integral_const_mul] at heq
  -- heq : I * ∫ ↑(ω f₀) * exp(I * ↑(ω h)) dμ = (-↑b) * ∫ exp(I * ↑(ω h)) dμ
  -- Multiply both sides by (-I) on the left to isolate the integral
  have hI_inv : -(Complex.I * Complex.I) = (1 : ℂ) := by
    simp
  have key := congr_arg ((-Complex.I) * ·) heq
  simp only [← mul_assoc, neg_mul, hI_inv, one_mul] at key
  -- key : ∫ ... = (-I) * ((-↑b) * ∫ exp(...) dμ)
  rw [key]; ring

/-! ## Leibniz rule for polynomial × exponential integrands

Generalizes `hasDerivAt_charFun_leibniz` to allow a polynomial weight P(ω)
that is constant in the differentiation parameter t. This is the key tool
for proving `gaussian_ibp_general` by induction. -/

/-- Leibniz rule for `∫ P(ω) * exp(I·ω(t·g+h)) dμ` at `t = 0`.

The polynomial weight P(ω) does not depend on t, so the derivative at t = 0
simply brings down `I·ω(g)` from the exponential. The domination bound
is `‖P(ω)‖ * ‖ω(g)‖`, integrable when P is a product of evaluation functionals. -/
private lemma hasDerivAt_weighted_exp_leibniz
    (P : Configuration E → ℂ)
    (hPm : AEStronglyMeasurable P (measure T))
    (g h : E)
    (hPint : Integrable (fun ω : Configuration E =>
      P ω * Complex.exp (Complex.I * ↑(ω h))) (measure T))
    (hbound : Integrable (fun ω : Configuration E => ‖P ω‖ * ‖ω g‖) (measure T)) :
    HasDerivAt
      (fun t : ℝ => ∫ ω : Configuration E,
        P ω * Complex.exp (Complex.I * ↑(ω (t • g + h))) ∂(measure T))
      (∫ ω : Configuration E,
        P ω * (Complex.I * ↑(ω g)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
      (0 : ℝ) := by
  have hleibniz := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (t : ℝ) (ω : Configuration E) =>
      P ω * Complex.exp (Complex.I * ↑(ω (t • g + h))))
    (F' := fun (t : ℝ) (ω : Configuration E) =>
      P ω * (Complex.I * ↑(ω g)) *
      Complex.exp (Complex.I * ↑(ω (t • g + h))))
    (x₀ := (0 : ℝ)) (bound := fun ω => ‖P ω‖ * ‖ω g‖) (s := Set.univ)
    -- (1) s ∈ 𝓝 0
    Filter.univ_mem
    -- (2) F t is a.e. strongly measurable
    (.of_forall fun t => hPm.mul (charFun_integrand_measurable T (t • g + h)))
    -- (3) F 0 is integrable
    (by simpa using hPint)
    -- (4) F' 0 is AEStronglyMeasurable
    (by
      simp only [zero_smul, zero_add]
      have hmeas_g : AEStronglyMeasurable (fun ω : Configuration E => (ω g : ℂ))
          (measure T) :=
        (Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable g)).aestronglyMeasurable
      exact (hPm.mul (hmeas_g.const_mul Complex.I)).mul
        (charFun_integrand_measurable T h))
    -- (5) ‖F' t ω‖ ≤ bound ω for all t ∈ s
    (.of_forall fun ω => by
      intro t _
      simp only [Complex.norm_mul, Complex.norm_I, Complex.norm_exp_I_mul_ofReal,
        Complex.norm_real, one_mul, mul_one, le_refl])
    -- (6) bound is integrable
    hbound
    -- (7) ∀ᵐ ω, ∀ t ∈ s, HasDerivAt (F · ω) (F' t ω) t
    (.of_forall fun ω => by
      intro t _
      have hlin : ∀ t', ω (t' • g + h) = t' * ω g + ω h := by
        intro t'; simp [map_add, map_smul]
      simp_rw [hlin]
      -- P(ω) is constant w.r.t. t, only the exp differentiates
      have hg : HasDerivAt (fun t' => t' * ω g + ω h) (ω g) t := by
        simpa using ((hasDerivAt_id t).mul_const (ω g)).add_const (ω h)
      have hc : HasDerivAt (fun t' => Complex.I * ↑(t' * ω g + ω h))
          (Complex.I * ↑(ω g)) t :=
        (HasDerivAt.ofReal_comp hg).const_mul Complex.I
      -- hc.cexp gives: HasDerivAt (exp ∘ (I * ↑(· * ωg + ωh)))
      --   (exp(I * ↑(t*ωg+ωh)) * (I * ↑(ωg))) t
      have hfinal := (hc.cexp).const_mul (P ω)
      -- hfinal : HasDerivAt (fun t' => P ω * exp(I * ↑(t'*ωg+ωh)))
      --   (P ω * (exp(...) * (I * ↑(ωg)))) t
      convert hfinal using 1; ring)
  convert hleibniz.2 using 2
  ext ω; simp

/-! ## Generalized Gaussian IBP

The key intermediate result: Gaussian IBP for polynomial × exponential
functionals. This extends `gaussian_ibp` to weighted integrals of the form
E[ω(f₀) · ∏ᵢ ω(gᵢ) · exp(iω(h))]. Setting h = 0 gives Wick's recursive formula.

The proof is by induction on the number of polynomial factors n.

**Base case (n = 0, one polynomial factor):**
Differentiate `gaussian_ibp T f₀ (t • g₀ + h)` at t = 0.
The Leibniz integral rule gives the LHS derivative, while the product rule on
⟨Tf₀, T(t·g₀+h)⟩ · i · charFun(t·g₀+h) gives the RHS derivative.
Equating and canceling i yields gaussian_ibp_general 0.

**Inductive step (n → n + 1):**
Let g_last = g(last) and g' = g ∘ castSucc (first n+1 factors).
Apply the IH with h replaced by t · g_last + h, then differentiate at t = 0.
The Leibniz rule brings down i·ω(g_last) in each integral. The product rule
on the boundary term produces two pieces: one fills in the last slot of the
sum, and the other becomes the new boundary term. -/

/-- Products of evaluation functionals are AEStronglyMeasurable. -/
private lemma prod_eval_aestronglyMeasurable (n : ℕ) (f : Fin n → E) :
    AEStronglyMeasurable (fun ω : Configuration E => ∏ i, (↑(ω (f i)) : ℂ))
      (measure T) := by
  apply Finset.aestronglyMeasurable_fun_prod
  intro i _
  exact (Complex.continuous_ofReal.measurable.comp
    (configuration_eval_measurable (f i))).aestronglyMeasurable

/-- Products of evaluation functionals times exponentials are integrable.
Follows from `product_integrable` and `‖exp(iω(h))‖ = 1`. -/
private lemma poly_exp_integrable (n : ℕ) (f : Fin n → E) (h : E) :
    Integrable (fun ω : Configuration E =>
      (∏ i, (↑(ω (f i)) : ℂ)) * Complex.exp (Complex.I * ↑(ω h)))
      (measure T) := by
  have hint := (product_integrable T n f).norm
  refine hint.mono
    ((prod_eval_aestronglyMeasurable T n f).mul (charFun_integrand_measurable T h))
    (.of_forall fun ω => ?_)
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  rw [show (∏ i, (↑(ω (f i)) : ℂ)) = ↑(∏ i, ω (f i)) from by push_cast; rfl,
    Complex.norm_real, norm_norm]

/-- The domination bound for applying Leibniz: `‖∏ ω(fᵢ)‖ * ‖ω(g)‖` is integrable. -/
private lemma poly_exp_bound_integrable (n : ℕ) (f : Fin n → E) (g : E) :
    Integrable (fun ω : Configuration E =>
      ‖∏ i, (↑(ω (f i)) : ℂ)‖ * ‖ω g‖)
      (measure T) := by
  -- ‖∏ ω(fᵢ)‖ * ‖ω g‖ = |∏ ω(fᵢ)| * |ω g| = ‖∏_{Fin(n+1)} ω(f'ᵢ)‖
  have h1 : ∀ ω : Configuration E,
      ‖∏ i, (↑(ω (f i)) : ℂ)‖ * ‖ω g‖ =
      ‖(∏ i : Fin n, ω (f i)) * ω g‖ := by
    intro ω
    rw [norm_mul, show (∏ i, (↑(ω (f i)) : ℂ)) = ↑(∏ i, ω (f i)) from
      by push_cast; rfl, Complex.norm_real]
  simp_rw [h1]
  let f' : Fin (n + 1) → E := Fin.cons g f
  have h2 : ∀ ω : Configuration E,
      (∏ i : Fin n, ω (f i)) * ω g = ∏ i : Fin (n + 1), ω (f' i) := by
    intro ω; simp only [f', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_comm]
  simp_rw [h2]
  exact (product_integrable T (n + 1) f').norm

/-- Weighted products of evaluation functionals times exponentials are integrable. -/
private lemma weighted_poly_exp_integrable (f₀ : E) (n : ℕ) (f : Fin n → E) (h : E) :
    Integrable (fun ω : Configuration E =>
      (↑(ω f₀) : ℂ) * (∏ i, (↑(ω (f i)) : ℂ)) *
      Complex.exp (Complex.I * ↑(ω h)))
      (measure T) := by
  let f' : Fin (n + 1) → E := Fin.cons f₀ f
  have hf : ∀ ω : Configuration E,
      (↑(ω f₀) : ℂ) * (∏ i, (↑(ω (f i)) : ℂ)) *
      Complex.exp (Complex.I * ↑(ω h)) =
      (∏ i : Fin (n + 1), (↑(ω (f' i)) : ℂ)) *
      Complex.exp (Complex.I * ↑(ω h)) := by
    intro ω; simp only [f', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [hf]
  exact poly_exp_integrable T (n + 1) f' h

/-- The weighted Leibniz domination bound: `‖↑(ω f₀) * ∏ ω(fᵢ)‖ * ‖ω g‖` is integrable. -/
private lemma weighted_poly_exp_bound_integrable (f₀ : E) (n : ℕ) (f : Fin n → E) (g : E) :
    Integrable (fun ω : Configuration E =>
      ‖(↑(ω f₀) : ℂ) * ∏ i, (↑(ω (f i)) : ℂ)‖ * ‖ω g‖)
      (measure T) := by
  -- ‖↑(ω f₀) * ∏ ω(fᵢ)‖ * ‖ω g‖ = |ω f₀ * ∏ ω(fᵢ)| * |ω g|
  -- = |ω f₀ * ∏ ω(fᵢ) * ω g| = ‖∏_{n+2 factors}‖
  have heq : ∀ ω : Configuration E,
      ‖(↑(ω f₀) : ℂ) * ∏ i, (↑(ω (f i)) : ℂ)‖ * ‖ω g‖ =
      ‖ω f₀ * (∏ i, ω (f i)) * ω g‖ := by
    intro ω
    rw [show (↑(ω f₀) : ℂ) * ∏ i, (↑(ω (f i)) : ℂ) =
      ↑(ω f₀ * ∏ i, ω (f i)) from by push_cast; ring, Complex.norm_real, ← norm_mul]
  simp_rw [heq]
  -- ω f₀ * ∏ ω(fᵢ) * ω g = ∏_{Fin(n+2)} ω(f_all i)
  let f_all : Fin (n + 2) → E := fun i =>
    if h : i.val = 0 then f₀
    else if h2 : i.val ≤ n then f ⟨i.val - 1, by omega⟩
    else g
  have hprod : ∀ ω : Configuration E,
      ω f₀ * (∏ i, ω (f i)) * ω g = ∏ i : Fin (n + 2), ω (f_all i) := by
    intro ω
    -- RHS = f_all(0) * ∏_{Fin(n+1)} f_all(succ i) = f₀ * ∏_{Fin(n+1)} f_all(succ i)
    rw [Fin.prod_univ_succ]
    simp only [f_all, Fin.val_zero, dite_true]
    -- Goal: ω f₀ * (∏ i, ω (f i)) * ω g = ω f₀ * ∏ i : Fin (n+1), ω(f_all(succ i))
    rw [mul_assoc]
    congr 1
    -- Goal: (∏ i, ω (f i)) * ω g = ∏ i : Fin (n+1), ω(f_all(succ i))
    rw [Fin.prod_univ_castSucc]
    -- RHS = (∏ i : Fin n, ω(f_all(succ(castSucc i)))) * ω(f_all(succ(last n)))
    congr 1
    · apply Finset.prod_congr rfl; intro i _
      simp only [f_all, Fin.val_succ, Fin.coe_castSucc, Nat.add_sub_cancel,
        show i.val + 1 ≠ 0 from by omega, dite_false,
        show i.val + 1 ≤ n from by omega, dite_true]
    · simp [f_all, Fin.val_last]
  simp_rw [hprod]
  exact (product_integrable T (n + 2) f_all).norm

/-- **Generalized Gaussian IBP** for polynomial × exponential functionals.

For a centered Gaussian with covariance C(f,g) = ⟨Tf,Tg⟩:

  E[ω(f₀) · ∏ᵢ ω(gᵢ) · exp(iω(h))]
  = ∑ⱼ C(f₀,gⱼ) · E[∏_{i≠j} ω(gᵢ) · exp(iω(h))]
    + C(f₀,h) · i · E[∏ᵢ ω(gᵢ) · exp(iω(h))]

Setting h = 0 gives `wick_recursive`.

Reference: Janson, "Gaussian Hilbert Spaces", Theorem 1.28;
Nualart, "The Malliavin Calculus and Related Topics", §1.3 (Stein identity). -/
theorem gaussian_ibp_general (n : ℕ) (f₀ : E) (g : Fin (n + 1) → E) (h : E) :
    ∫ ω : Configuration E,
      ↑(ω f₀) * (∏ i, (↑(ω (g i)) : ℂ)) *
      Complex.exp (Complex.I * ↑(ω h)) ∂(measure T) =
    ∑ j : Fin (n + 1), ↑(@inner ℝ H _ (T f₀) (T (g j))) *
      ∫ ω : Configuration E,
        (∏ i : Fin n, (↑(ω (g (Fin.succAbove j i))) : ℂ)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂(measure T)
    + ↑(@inner ℝ H _ (T f₀) (T h)) * Complex.I *
      ∫ ω : Configuration E,
        (∏ i, (↑(ω (g i)) : ℂ)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂(measure T) := by
  induction n generalizing h with
  | zero =>
    -- Simplify Fin products/sums under binders
    simp only [Fin.prod_univ_zero, one_mul]
    -- Goal: ∫ ↑(ωf₀) * ↑(ωg₀) * exp(I*↑(ωh)) dμ
    -- = ↑⟨Tf₀,Tg₀⟩ * ∫ exp dμ + ↑⟨Tf₀,Th⟩ * I * ∫ ↑(ωg₀)*exp dμ
    -- Strategy: G(t) = A(t)*B(t) where A(t)=↑⟨Tf₀,T(t•g₀+h)⟩, B(t)=charFun(t•g₀+h)
    -- G(t) = (-I) * F(t) where F(t) = ∫ ↑(ωf₀)*exp(I*ω(t•g₀+h))  [by gaussian_ibp]
    -- Differentiate G two ways, equate via HasDerivAt.unique.

    -- Step 1: HasDerivAt for A(t) = (↑⟨Tf₀, T(t•g₀+h)⟩ : ℂ)
    have hA : HasDerivAt (fun t : ℝ =>
        (↑(@inner ℝ H _ (T f₀) (T (t • g 0 + h))) : ℂ))
        (↑(@inner ℝ H _ (T f₀) (T (g 0)))) (0 : ℝ) := by
      have hlin : ∀ t : ℝ, @inner ℝ H _ (T f₀) (T (t • g 0 + h)) =
          t * @inner ℝ H _ (T f₀) (T (g 0)) + @inner ℝ H _ (T f₀) (T h) := by
        intro t; simp [map_add, map_smul, inner_add_right, inner_smul_right]
      simp_rw [hlin]
      convert (((hasDerivAt_id (0 : ℝ)).mul_const _).add_const
        (@inner ℝ H _ (T f₀) (T h))).ofReal_comp using 1
      push_cast; ring
    -- Step 2: HasDerivAt for B(t) = ∫ exp(I*↑(ω(t•g₀+h))) dμ
    have hB := hasDerivAt_charFun_leibniz T (g 0) h
    -- Step 3: Product rule for G(t) = A(t) * B(t)
    have hG_prod := hA.mul hB
    -- Step 4: Leibniz for F(t) = ∫ ↑(ωf₀) * exp(I*ω(t•g₀+h)) dμ
    have hF := hasDerivAt_weighted_exp_leibniz T
      (fun ω => ↑(ω f₀))
      ((Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable f₀)).aestronglyMeasurable)
      (g 0) h
      ((pairing_integrable T f₀).mono
        ((Complex.continuous_ofReal.measurable.comp
          (configuration_eval_measurable f₀)).aestronglyMeasurable.mul
          (charFun_integrand_measurable T h))
        (.of_forall fun ω => by
          simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, Complex.norm_real, mul_one, le_refl]))
      (by
        have : Integrable (fun ω : Configuration E => ω f₀ * ω (g 0)) (measure T) := by
          have h2 : (fun ω : Configuration E => ω f₀ * ω (g 0)) =
              (fun ω => ∏ i : Fin 2, ω (![f₀, g 0] i)) := by
            ext ω; simp [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
          rw [h2]; exact product_integrable T 2 _
        exact this.norm.congr (.of_forall fun ω => by
          simp only [norm_mul, Complex.norm_real]))
    -- Step 5: Scale F by (-I) to get G
    have hG_leib := hF.const_mul (-Complex.I)
    -- Show (-I) * F(t) = A(t) * B(t) using gaussian_ibp
    have hfun_eq : (fun (t : ℝ) => (-Complex.I) * ∫ ω : Configuration E,
          ↑(ω f₀) * Complex.exp (Complex.I * ↑(ω (t • g 0 + h))) ∂measure T) =
        (fun (t : ℝ) => (↑(@inner ℝ H _ (T f₀) (T (t • g 0 + h))) : ℂ) *
          ∫ ω, Complex.exp (Complex.I * ↑(ω (t • g 0 + h))) ∂measure T) := by
      ext t; rw [gaussian_ibp T f₀ (t • g 0 + h)]
      have h1 : -Complex.I * (↑(@inner ℝ H _ (T f₀) (T (t • g 0 + h))) * Complex.I *
          ∫ ω, Complex.exp (Complex.I * ↑(ω (t • g 0 + h))) ∂measure T) =
        ↑(@inner ℝ H _ (T f₀) (T (t • g 0 + h))) * (-(Complex.I * Complex.I)) *
          ∫ ω, Complex.exp (Complex.I * ↑(ω (t • g 0 + h))) ∂measure T := by ring
      rw [h1, Complex.I_mul_I]; ring
    rw [hfun_eq] at hG_leib
    -- Step 6: Equate derivatives
    have hderiv := hG_leib.unique hG_prod
    -- Simplify 0 • g 0 + h → h
    simp only [zero_smul, zero_add] at hderiv
    -- Step 7: Rewrite integrands in hderiv to match the goal
    -- Pull I out of each integrand using integral_const_mul
    have h_lhs : ∫ ω : Configuration E,
        ↑(ω f₀) * (Complex.I * ↑(ω (g 0))) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T =
      Complex.I * ∫ ω : Configuration E, ↑(ω f₀) * ↑(ω (g 0)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T := by
      rw [← integral_const_mul]; congr 1; ext ω; ring
    have h_rhs : ∫ ω : Configuration E,
        Complex.I * ↑(ω (g 0)) * Complex.exp (Complex.I * ↑(ω h)) ∂measure T =
      Complex.I * ∫ ω : Configuration E,
        ↑(ω (g 0)) * Complex.exp (Complex.I * ↑(ω h)) ∂measure T := by
      rw [← integral_const_mul]; congr 1; ext ω; ring
    rw [h_lhs, h_rhs] at hderiv
    -- hderiv : -I * (I * ∫ f₀*g₀*exp) = ↑c₁ * ∫ exp + ↑c₂ * (I * ∫ g₀*exp)
    -- Cancel -I*I on LHS
    have hII : ∀ (x : ℂ), -Complex.I * (Complex.I * x) = x := by
      intro x; rw [← mul_assoc, show (-Complex.I) * Complex.I = (1 : ℂ) from
        by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
    rw [hII] at hderiv
    -- hderiv : ∫ f₀*g₀*exp = ↑c₁ * ∫ exp + ↑c₂ * (I * ∫ g₀*exp)
    -- Goal has ∏ i : Fin (0+1), ..., ∑ j : Fin (0+1), ..., ∏ i : Fin 0, ...
    -- Simplify these in the goal, then match hderiv
    have hg1 : ∀ ω : Configuration E,
        (↑(ω f₀) * ∏ i, (↑(ω (g i)) : ℂ)) *
        Complex.exp (Complex.I * ↑(ω h)) =
        ↑(ω f₀) * ↑(ω (g 0)) * Complex.exp (Complex.I * ↑(ω h)) := by
      intro ω; simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    have hg2 : ∀ ω : Configuration E,
        (∏ i, (↑(ω (g i)) : ℂ)) * Complex.exp (Complex.I * ↑(ω h)) =
        ↑(ω (g 0)) * Complex.exp (Complex.I * ↑(ω h)) := by
      intro ω; simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    simp_rw [hg1, hg2]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    convert hderiv using 1; ring
  | succ n ih =>
    -- We need to show the statement for n+2 polynomial factors.
    -- Strategy: apply IH with h replaced by t·g_last + h, differentiate at t=0.
    -- Define g' = first n+1 factors, g_last = last factor
    set g_last : E := g (Fin.last (n + 1)) with hg_last_def
    set g' : Fin (n + 1) → E := g ∘ Fin.castSucc with hg'_def
    -- Product splitting: ∏_{Fin(n+2)} ω(gᵢ) = (∏_{Fin(n+1)} ω(g'ᵢ)) * ω(g_last)
    have hprod_split : ∀ ω : Configuration E,
        (∏ i : Fin (n + 2), (↑(ω (g i)) : ℂ)) =
        (∏ i : Fin (n + 1), (↑(ω (g' i)) : ℂ)) * ↑(ω g_last) := by
      intro ω
      rw [Fin.prod_univ_castSucc]; rfl
    -- The IH for any h':
    -- ih : ∀ g' h', ∫ ω(f₀) * ∏_{n+1} ω(g'ᵢ) * exp(iω(h')) =
    --   ∑_j ⟨Tf₀,Tg'_j⟩ * ∫ ∏_{n} ω(g'(sA j)) * exp(iω(h'))
    --   + ⟨Tf₀,Th'⟩ * I * ∫ ∏_{n+1} ω(g'ᵢ) * exp(iω(h'))
    -- Instantiate with h' = t • g_last + h:
    have ih_t : ∀ (t : ℝ),
        ∫ ω : Configuration E,
          ↑(ω f₀) * (∏ i, (↑(ω (g' i)) : ℂ)) *
          Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T) =
        ∑ j : Fin (n + 1), ↑(@inner ℝ H _ (T f₀) (T (g' j))) *
          ∫ ω : Configuration E,
            (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T)
        + ↑(@inner ℝ H _ (T f₀) (T (t • g_last + h))) * Complex.I *
          ∫ ω : Configuration E,
            (∏ i, (↑(ω (g' i)) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T) :=
      fun t => ih g' (t • g_last + h)
    -- Now differentiate both sides at t = 0.
    -- LHS derivative using hasDerivAt_weighted_exp_leibniz:
    have hLHS := hasDerivAt_weighted_exp_leibniz T
      (fun ω => (↑(ω f₀) : ℂ) * ∏ i, (↑(ω (g' i)) : ℂ))
      ((Complex.continuous_ofReal.measurable.comp
        (configuration_eval_measurable f₀)).aestronglyMeasurable.mul
        (prod_eval_aestronglyMeasurable T (n + 1) g'))
      g_last h
      (weighted_poly_exp_integrable T f₀ (n + 1) g' h)
      (by
        exact weighted_poly_exp_bound_integrable T f₀ (n + 1) g' g_last)
    -- hLHS : HasDerivAt (fun t => ∫ ω(f₀) * ∏g' * exp(iω(t·g_last+h)))
    --   (∫ ω(f₀) * ∏g' * (I·ω(g_last)) * exp(iω(h))) 0
    -- By ih_t, both sides of ih_t are equal for all t, so have same derivative.
    -- Use hasDerivAt_of_eq to transfer the derivative from hLHS to the RHS.
    have hRHS_eq : HasDerivAt
      (fun (t : ℝ) =>
        ∑ j : Fin (n + 1), ↑(@inner ℝ H _ (T f₀) (T (g' j))) *
          ∫ ω : Configuration E,
            (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T)
        + ↑(@inner ℝ H _ (T f₀) (T (t • g_last + h))) * Complex.I *
          ∫ ω : Configuration E,
            (∏ i, (↑(ω (g' i)) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T))
      (∫ ω : Configuration E,
        (fun ω => ↑(ω f₀) * ∏ i, (↑(ω (g' i)) : ℂ)) ω *
        (Complex.I * ↑(ω g_last)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
      (0 : ℝ) := by
      rw [show (fun (t : ℝ) => ∑ j : Fin (n + 1), _ + _) =
        (fun (t : ℝ) => ∫ ω : Configuration E,
          ↑(ω f₀) * (∏ i, (↑(ω (g' i)) : ℂ)) *
          Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T)) from
        funext fun t => (ih_t t).symm]
      exact hLHS
    -- Also compute the RHS derivative independently using sum/product differentiation
    -- Each summand A_j(t) = ∫ ∏_n g'(sA j) * exp(iω(t·g_last+h))
    -- is differentiable by hasDerivAt_weighted_exp_leibniz
    have hA_j : ∀ j : Fin (n + 1), HasDerivAt
        (fun (t : ℝ) => ∫ ω : Configuration E,
          (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
          Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T))
        (∫ ω : Configuration E,
          (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
          (Complex.I * ↑(ω g_last)) *
          Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
        (0 : ℝ) := by
      intro j
      exact hasDerivAt_weighted_exp_leibniz T
        (fun ω => ∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ))
        (prod_eval_aestronglyMeasurable T n (g' ∘ Fin.succAbove j))
        g_last h
        (poly_exp_integrable T n (g' ∘ Fin.succAbove j) h)
        (poly_exp_bound_integrable T n (g' ∘ Fin.succAbove j) g_last)
    -- B(t) = ⟨Tf₀, T(t·g_last+h)⟩ is affine in t
    have hB : HasDerivAt
        (fun (t : ℝ) => (↑(@inner ℝ H _ (T f₀) (T (t • g_last + h))) : ℂ))
        (↑(@inner ℝ H _ (T f₀) (T g_last)))
        (0 : ℝ) := by
      have hlin : ∀ t : ℝ, @inner ℝ H _ (T f₀) (T (t • g_last + h)) =
          t * @inner ℝ H _ (T f₀) (T g_last) + @inner ℝ H _ (T f₀) (T h) := by
        intro t; simp [map_add, map_smul, inner_add_right, inner_smul_right]
      simp_rw [hlin]
      convert (((hasDerivAt_id (0 : ℝ)).mul_const _).add_const
        (@inner ℝ H _ (T f₀) (T h))).ofReal_comp using 1
      push_cast; ring
    -- C(t) = ∫ ∏ ω(g'ᵢ) * exp(iω(t·g_last+h)) dμ
    have hC : HasDerivAt
        (fun (t : ℝ) => ∫ ω : Configuration E,
          (∏ i, (↑(ω (g' i)) : ℂ)) *
          Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T))
        (∫ ω : Configuration E,
          (∏ i, (↑(ω (g' i)) : ℂ)) * (Complex.I * ↑(ω g_last)) *
          Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
        (0 : ℝ) :=
      hasDerivAt_weighted_exp_leibniz T
        (fun ω => ∏ i, (↑(ω (g' i)) : ℂ))
        (prod_eval_aestronglyMeasurable T (n + 1) g')
        g_last h
        (poly_exp_integrable T (n + 1) g' h)
        (poly_exp_bound_integrable T (n + 1) g' g_last)
    -- Combine: RHS(t) = ∑_j c_j * A_j(t) + (B(t) * I) * C(t)
    -- HasDerivAt for the sum part
    have hSum : HasDerivAt
        (fun (t : ℝ) => ∑ j : Fin (n + 1), ↑(@inner ℝ H _ (T f₀) (T (g' j))) *
          ∫ ω : Configuration E,
            (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T))
        (∑ j : Fin (n + 1), ↑(@inner ℝ H _ (T f₀) (T (g' j))) *
          ∫ ω : Configuration E,
            (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
            (Complex.I * ↑(ω g_last)) *
            Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
        (0 : ℝ) :=
      by
        have h_sum := HasDerivAt.sum (fun j (_ : j ∈ Finset.univ) =>
          (hA_j j).const_mul (↑(@inner ℝ H _ (T f₀) (T (g' j)))))
        convert h_sum using 1; ext; simp [Finset.sum_apply]
    -- HasDerivAt for the product part B(t) * I * C(t)
    have hProd : HasDerivAt
        (fun (t : ℝ) => ↑(@inner ℝ H _ (T f₀) (T (t • g_last + h))) * Complex.I *
          ∫ ω : Configuration E,
            (∏ i, (↑(ω (g' i)) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (t • g_last + h))) ∂(measure T))
        (↑(@inner ℝ H _ (T f₀) (T g_last)) * Complex.I *
          ∫ ω : Configuration E,
            (∏ i, (↑(ω (g' i)) : ℂ)) *
            Complex.exp (Complex.I * ↑(ω (0 • g_last + h))) ∂(measure T)
        + ↑(@inner ℝ H _ (T f₀) (T (0 • g_last + h))) * Complex.I *
          ∫ ω : Configuration E,
            (∏ i, (↑(ω (g' i)) : ℂ)) * (Complex.I * ↑(ω g_last)) *
            Complex.exp (Complex.I * ↑(ω h)) ∂(measure T))
        (0 : ℝ) := by
      have h1 := (hB.mul_const Complex.I).mul hC
      convert h1 using 1; simp only [zero_smul, zero_add]
    have hRHS_indep := hSum.add hProd
    -- Now use HasDerivAt.unique to equate the two derivatives
    have hderiv_eq := hRHS_eq.unique hRHS_indep
    -- hderiv_eq equates the derivative from hRHS_eq with the one from hRHS_indep
    -- Simplify 0 • g_last + h → h in hderiv_eq
    simp only [zero_smul, zero_add] at hderiv_eq
    -- hderiv_eq : ∫ ω(f₀) * ∏g' * (I·ωg_last) * exp(iωh) =
    --   ∑_j c_j * ∫ ∏_n g'(sA j) * (I·ωg_last) * exp
    --   + c_h * I * ∫ ∏g' * exp
    --   + c_h * I * ∫ ∏g' * (I·ωg_last) * exp
    -- Multiply both sides by (-I) to get the desired identity
    -- First, rewrite the LHS of the goal using hprod_split
    -- LHS goal: ∫ ω(f₀) * ∏_{n+2} * exp
    -- = (-I) * I * ∫ ω(f₀) * ∏_{n+2} * exp  (since -I*I = 1)
    -- = (-I) * ∫ ω(f₀) * ∏g' * (I*ωg_last) * exp  (by pulling I*ωg_last back)
    -- = (-I) * (RHS of hderiv_eq)
    -- This gives us the desired sum + boundary term
    -- hderiv_eq gives us the key identity. Now extract the goal.
    -- Step 1: Pull I out of integrands using integral_const_mul
    -- LHS of hderiv_eq: ∫ (ω(f₀) * ∏g') * (I*ωg_last) * exp
    --   = I * ∫ ω(f₀) * ∏g' * ωg_last * exp  (by pulling I out)
    --   = I * ∫ ω(f₀) * ∏_{n+2}g * exp  (by hprod_split)
    have hI_lhs : ∫ ω : Configuration E,
        (↑(ω f₀) * ∏ i, (↑(ω (g' i)) : ℂ)) * (Complex.I * ↑(ω g_last)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T =
      Complex.I * ∫ ω : Configuration E,
        (↑(ω f₀) * ∏ i, (↑(ω (g i)) : ℂ)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T := by
      rw [← integral_const_mul]; congr 1; ext ω
      rw [hprod_split ω]; ring
    -- Each summand RHS: ∫ ∏g'(sA j) * (I*ωg_last) * exp
    --   = I * ∫ ∏g'(sA j) * ωg_last * exp
    have hI_sum : ∀ j : Fin (n + 1),
        ∫ ω : Configuration E,
          (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) *
          (Complex.I * ↑(ω g_last)) *
          Complex.exp (Complex.I * ↑(ω h)) ∂measure T =
        Complex.I * ∫ ω : Configuration E,
          (∏ i : Fin n, (↑(ω (g' (Fin.succAbove j i))) : ℂ)) * ↑(ω g_last) *
          Complex.exp (Complex.I * ↑(ω h)) ∂measure T := by
      intro j; rw [← integral_const_mul]; congr 1; ext ω; ring
    -- Last integrand: ∫ ∏g' * (I*ωg_last) * exp = I * ∫ ∏_{n+2}g * exp
    have hI_last : ∫ ω : Configuration E,
        (∏ i, (↑(ω (g' i)) : ℂ)) * (Complex.I * ↑(ω g_last)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T =
      Complex.I * ∫ ω : Configuration E,
        (∏ i, (↑(ω (g i)) : ℂ)) *
        Complex.exp (Complex.I * ↑(ω h)) ∂measure T := by
      rw [← integral_const_mul]; congr 1; ext ω
      rw [hprod_split ω]; ring
    rw [hI_lhs] at hderiv_eq
    simp_rw [hI_sum] at hderiv_eq
    rw [hI_last] at hderiv_eq
    -- hderiv_eq:
    -- I * LHS = ∑_j c_j * (I * ∫ ∏_n g'(sA j) * g_last * exp)
    --   + c_last * I * ∫ ∏g' * exp + c_h * I * (I * ∫ ∏_{n+2} * exp)
    -- Multiply both sides by (-I) to cancel
    have hII : ∀ (x : ℂ), -Complex.I * (Complex.I * x) = x := by
      intro x; rw [← mul_assoc, show (-Complex.I) * Complex.I = (1 : ℂ) from
        by rw [neg_mul, Complex.I_mul_I, neg_neg], one_mul]
    have hderiv2 := congr_arg ((-Complex.I) * ·) hderiv_eq
    simp only [hII, mul_add] at hderiv2
    -- Step 1: Product reindexing — relate g/g'/g_last via succAbove
    -- For j = last: succAbove(last) = castSucc, so ∏ g(sA(last) i) = ∏ g'
    have hprod_last_sA : ∀ (ω : Configuration E),
        (∏ i : Fin (n + 1), (↑(ω (g ((Fin.last (n + 1)).succAbove i))) : ℂ)) =
        ∏ i : Fin (n + 1), (↑(ω (g' i)) : ℂ) := by
      intro ω; congr 1; ext i; simp [Fin.succAbove_last, hg'_def]
    -- For j = castSucc j': ∏_{n+1} g(sA(castSucc j') i) = ∏_n g'(sA j' i) * g_last
    have hprod_castSucc_sA : ∀ (j : Fin (n + 1)) (ω : Configuration E),
        (∏ i : Fin (n + 1), (↑(ω (g ((Fin.castSucc j).succAbove i))) : ℂ)) =
        (∏ i : Fin n, (↑(ω (g' (j.succAbove i))) : ℂ)) * ↑(ω g_last) := by
      intro j ω
      rw [Fin.prod_univ_castSucc]
      congr 1
      · congr 1; ext i
        simp only [Fin.castSucc_succAbove_castSucc, hg'_def, Function.comp]
      · congr 2
        rw [Fin.succAbove_ne_last_last (by simp [Fin.ext_iff, Fin.val_last, Fin.val_castSucc]; omega)]
    -- Step 2: Rewrite the goal sum using Fin.sum_univ_castSucc + product reindexing
    rw [Fin.sum_univ_castSucc]
    simp_rw [hprod_castSucc_sA, hprod_last_sA]
    -- Step 3: Cancel I by multiplying both sides
    -- Use hderiv_eq: I * LHS = hderiv_eq_RHS, then show I * goal_RHS = hderiv_eq_RHS
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [hderiv_eq]
    -- Distribute I on the RHS
    rw [mul_add, mul_add, Finset.mul_sum]
    -- Fold g(castSucc i) → g' i and g(last) → g_last on the RHS
    simp only [show ∀ i, g (Fin.castSucc i) = g' i from fun _ => rfl,
               show g (Fin.last (n + 1)) = g_last from rfl]
    -- Normalize + association and match termwise
    simp only [add_assoc]
    congr 1
    · congr 1; ext j; ring
    · ring

/-! ## Wick's theorem — recursive form

The recursive form avoids the combinatorial overhead of enumerating
perfect pairings. It says: pick any index (we use 0), then the
(n+2)-point function equals the sum over all partners j for index 0.

The proof of the base case n = 0 uses `cross_moment_eq_covariance`.
For n ≥ 1, the proof follows from `gaussian_ibp_general` with h = 0,
which eliminates the exponential factor and reduces to the polynomial case. -/

/-- **Wick's theorem (recursive form).**

For a centered Gaussian measure with covariance C(f,g) = ⟨Tf, Tg⟩_H:

  E[ω(f₀) · ∏ⱼ ω(gⱼ)] = ∑ⱼ C(f₀, gⱼ) · E[∏_{i≠j} ω(gᵢ)]

The base case n = 0 is `cross_moment_eq_covariance`. The general case follows
from `gaussian_ibp_general` specialized to h = 0 (see above for proof sketch). -/
theorem wick_recursive (n : ℕ) (f₀ : E) (g : Fin (n + 1) → E) :
    ∫ ω : Configuration E, ω f₀ * ∏ i, ω (g i) ∂(measure T) =
      ∑ j : Fin (n + 1), @inner ℝ H _ (T f₀) (T (g j)) *
        ∫ ω : Configuration E, ∏ i : Fin n,
          ω (g (Fin.succAbove j i)) ∂(measure T) := by
  cases n with
  | zero =>
    -- n = 0: ∫ ω(f₀)·ω(g₀) dμ = ⟨Tf₀,T(g₀)⟩ · ∫ 1 dμ = ⟨Tf₀,T(g₀)⟩
    simp only [Fin.prod_univ_one, Fin.sum_univ_one, Nat.reduceAdd]
    simp_rw [Fin.prod_univ_zero]
    rw [integral_const, probReal_univ, one_smul, mul_one]
    exact cross_moment_eq_covariance T f₀ (g 0)
  | succ n =>
    -- For n ≥ 1: follows from gaussian_ibp_general with h = 0.
    -- Setting h = 0 eliminates the exponential (exp(0)=1) and the last term
    -- (⟨Tf₀,T(0)⟩ = 0), giving the ℂ version of this identity.
    -- The ℝ version follows by Complex.ofReal injectivity, using
    -- Complex.ofRealCLM.integral_comp_comm to commute ↑ with ∫.
    have h_gen := gaussian_ibp_general T (n + 1) f₀ g 0
    simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      inner_zero_right, Complex.ofReal_zero, zero_mul, add_zero] at h_gen
    -- Helper: lift ∫ ∏ ω(fᵢ) from ℝ to ℂ via Complex.ofRealCLM.integral_comp_comm
    have lift : ∀ (m : ℕ) (f : Fin m → E),
        (↑(∫ ω : Configuration E, ∏ i, ω (f i) ∂measure T) : ℂ) =
        ∫ ω, ∏ i, (↑(ω (f i)) : ℂ) ∂measure T := by
      intro m f
      change Complex.ofRealCLM _ = _
      rw [← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM (product_integrable T m f)]
      congr 1; ext ω; simp +decide
    apply Complex.ofReal_injective
    -- LHS: lift ∫ ω(f₀) * ∏ ω(gᵢ) to ℂ
    have lhs_eq : (↑(∫ ω : Configuration E, ω f₀ * ∏ i, ω (g i) ∂measure T) : ℂ) =
        ∫ ω, ↑(ω f₀) * ∏ i, (↑(ω (g i)) : ℂ) ∂measure T := by
      change Complex.ofRealCLM _ = _
      rw [← ContinuousLinearMap.integral_comp_comm]
      · congr 1; ext ω; simp +decide
      · -- Rewrite as a product over Fin (n+3) for integrability
        let f' : Fin (n + 3) → E := @Fin.cons (n + 2) (fun _ => E) f₀ g
        have heq : (fun ω : Configuration E => ω f₀ * ∏ i, ω (g i)) =
            fun ω => ∏ i : Fin (n + 3), ω (f' i) := by
          ext ω; simp only [f', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        rw [heq]; exact product_integrable T (n + 3) f'
    rw [lhs_eq, h_gen, Complex.ofReal_sum]
    congr 1; ext j; rw [Complex.ofReal_mul]
    congr 1
    exact (lift (n + 1) (fun i => g (j.succAbove i))).symm

/-! ## Odd moments vanish

For a centered Gaussian measure, all odd-order moments are zero.
This follows from `wick_recursive` by induction on k. -/

/-- Odd moments of a centered Gaussian measure vanish.

Proof by induction on k using `wick_recursive`:
- Base case (k=0): `∫ ω(f₀) dμ = 0` by `measure_centered`.
- Step (k → k+1): Write `∫ ∏_{i≤2k+2} ω(fᵢ) = ∫ ω(f₀) · ∏_{i=1}^{2k+2} ω(fᵢ)`.
  By `wick_recursive`, this equals `∑ⱼ ⟨Tf₀,Tfⱼ⟩ · ∫ ∏_{i≠0,j} ω(fᵢ)`.
  Each inner integral is over 2k+1 variables (odd), so vanishes by IH. -/
theorem odd_moment_vanish (k : ℕ) (f : Fin (2 * k + 1) → E) :
    ∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T) = 0 := by
  induction k with
  | zero =>
    simp only [Fin.prod_univ_one, Nat.reduceMul, Nat.reduceAdd]
    exact measure_centered T (f 0)
  | succ k ih =>
    -- Split: ∏_{Fin(2k+3)} = ω(f 0) * ∏_{Fin(2k+2)}
    simp_rw [Fin.prod_univ_succ]
    change ∫ ω : Configuration E, ω (f 0) *
      ∏ i : Fin ((2 * k + 1) + 1), ω (f (Fin.succ i)) ∂(measure T) = 0
    -- Apply wick_recursive: ∑ⱼ ⟨Tf₀,Tgⱼ⟩ · ∫∏_{i≠j}ω(gᵢ)
    rw [wick_recursive T (2 * k + 1) (f 0) (fun i => f i.succ)]
    -- Each inner integral is over 2k+1 terms (odd), vanishes by IH
    apply Finset.sum_eq_zero
    intro j _
    have := ih (fun i => f ((Fin.succAbove j i).succ))
    rw [this]; simp

/-! ## Wick bound

The bound on n-point functions follows from Wick's recursive formula
by induction, using Cauchy-Schwarz at each step. The (2k-1)!! factor
counts the number of perfect pairings of 2k elements. -/

/-- **Wick bound on n-point functions.**

  |E[∏ᵢ ω(fᵢ)]| ≤ (n-1)‼ · ∏ᵢ ‖T(fᵢ)‖

For odd n, both sides are zero (LHS by `odd_moment_vanish`, RHS by
convention (n-1)‼ for n=1 gives 0‼ = 1, but we use the general bound).

For even n = 2k, the (2k-1)‼ = (2k-1)(2k-3)···3·1 counts the number
of perfect pairings. Each pairing contributes ∏ |C(fᵢ,fⱼ)| ≤ ∏ ‖Tfᵢ‖·‖Tfⱼ‖
by Cauchy-Schwarz, so the total is ≤ (2k-1)‼ · ∏ ‖Tfᵢ‖.

This bound directly implies OS1' with γ = 1/2, since
(2k-1)‼ ≤ (2k)!^{1/2} and (2k)! ≤ (2k)^{2k}. More precisely,
(2k)! = (2k)‼ · (2k-1)‼ = 2^k · k! · (2k-1)‼, so
(2k-1)‼ = (2k)! / (2^k · k!) ≤ (2k)!^{1/2}. -/
theorem wick_bound : ∀ (n : ℕ) (f : Fin n → E),
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖
  | 0, f => by simp [Finset.prod_empty]
  | 1, f => by
    simp only [Nat.reduceSub, Fin.prod_univ_one]
    rw [measure_centered T (f 0)]
    simp
  | n + 2, f => by
    -- Split product once: ∏_{Fin(n+2)} ω(f i) = ω(f 0) * ∏_{Fin(n+1)} ω(f(succ i))
    have hsplit : (fun ω : Configuration E => ∏ i : Fin (n + 2), ω (f i)) =
        (fun ω => ω (f 0) * ∏ i : Fin (n + 1), ω (f i.succ)) := by
      ext ω; exact Fin.prod_univ_succ _
    simp only [hsplit]
    -- Apply Wick recursion
    rw [wick_recursive T n (f 0) (fun i => f i.succ)]
    -- Bound each summand
    have bound : ∀ j : Fin (n + 1),
        ‖@inner ℝ H _ (T (f 0)) (T (f j.succ)) *
          ∫ ω, ∏ i : Fin n, ω (f (j.succAbove i).succ) ∂(measure T)‖ ≤
        ((n - 1).doubleFactorial : ℝ) * ∏ i : Fin (n + 2), ‖T (f i)‖ := by
      intro j
      rw [norm_mul]
      -- Cauchy-Schwarz: ‖⟨Tf₀, Tgⱼ⟩‖ ≤ ‖Tf₀‖ * ‖Tgⱼ‖
      have hCS := norm_inner_le_norm (𝕜 := ℝ) (T (f 0)) (T (f j.succ))
      -- IH on the n-point function
      have hIH := wick_bound n (fun i => f (j.succAbove i).succ)
      -- Product rearrangement: ‖T(f(j+1))‖ * ∏_{complement} = ∏_{Fin(n+1)} ‖T(f(succ i))‖
      have hprod : ‖T (f j.succ)‖ * ∏ i : Fin n, ‖T (f (j.succAbove i).succ)‖ =
          ∏ i : Fin (n + 1), ‖T (f i.succ)‖ :=
        (Fin.prod_univ_succAbove (fun i => ‖T (f i.succ)‖) j).symm
      calc ‖@inner ℝ H _ (T (f 0)) (T (f j.succ))‖ *
              ‖∫ ω, ∏ i, ω (f (j.succAbove i).succ) ∂(measure T)‖
          ≤ (‖T (f 0)‖ * ‖T (f j.succ)‖) *
            ((n - 1).doubleFactorial * ∏ i, ‖T (f (j.succAbove i).succ)‖) :=
            mul_le_mul hCS hIH (norm_nonneg _) (by positivity)
        _ = (n - 1).doubleFactorial *
            (‖T (f 0)‖ * (‖T (f j.succ)‖ * ∏ i, ‖T (f (j.succAbove i).succ)‖)) := by ring
        _ = (n - 1).doubleFactorial * (‖T (f 0)‖ * ∏ i : Fin (n + 1), ‖T (f i.succ)‖) := by
            rw [hprod]
        _ = ((n - 1).doubleFactorial : ℝ) * ∏ i : Fin (n + 2), ‖T (f i)‖ := by
            congr 1; exact (Fin.prod_univ_succ (fun i => ‖T (f i)‖)).symm
    -- Triangle inequality + sum of (n+1) identical bounds
    have h1 := norm_sum_le (Finset.univ : Finset (Fin (n + 1)))
      (fun j => @inner ℝ H _ (T (f 0)) (T (f j.succ)) *
        ∫ ω, ∏ i : Fin n, ω (f (j.succAbove i).succ) ∂(measure T))
    have h2 : ∑ j : Fin (n + 1),
        ‖@inner ℝ H _ (T (f 0)) (T (f j.succ)) *
          ∫ ω, ∏ i : Fin n, ω (f (j.succAbove i).succ) ∂(measure T)‖ ≤
        ∑ _j : Fin (n + 1),
          ((n - 1).doubleFactorial * ∏ i : Fin (n + 2), ‖T (f i)‖) :=
      Finset.sum_le_sum (fun j _ => bound j)
    have h3 : ∑ _j : Fin (n + 1),
        ((n - 1).doubleFactorial * ∏ i : Fin (n + 2), ‖T (f i)‖ : ℝ) =
      ((n + 2) - 1).doubleFactorial * ∏ i : Fin (n + 2), ‖T (f i)‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
        show (n + 2 : ℕ) - 1 = n + 1 from by omega]
      rw [Nat.doubleFactorial_add_one n]
      push_cast; ring
    exact le_trans h1 (le_trans h2 h3.le)

/-! ## Corollary: OS1' Schwinger growth for GFF

The Wick bound directly gives the factorial growth condition OS1'
with γ = 1/2, using the inequality (n-1)‼ ≤ n!^{1/2}. -/

end GaussianField

/-- Helper: m‼² ≤ (m+1)! for all m.

Proof by induction on m with step 2, using (m+2)‼ = (m+2)·m‼:
  ((m+2)‼)² = (m+2)²·(m‼)² ≤ (m+2)²·(m+1)! ≤ (m+3)·(m+2)·(m+1)! = (m+3)! -/
private lemma dfact_sq_le_succ_fact : ∀ m : ℕ, m.doubleFactorial ^ 2 ≤ (m + 1).factorial
  | 0 => by norm_num
  | 1 => by norm_num
  | m + 2 => by
    rw [Nat.doubleFactorial_add_two, mul_pow]
    calc (m + 2) ^ 2 * m.doubleFactorial ^ 2
        ≤ (m + 2) ^ 2 * (m + 1).factorial :=
          Nat.mul_le_mul_left _ (dfact_sq_le_succ_fact m)
      _ = (m + 2) * ((m + 2) * (m + 1).factorial) := by ring
      _ ≤ (m + 3) * ((m + 2) * (m + 1).factorial) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (m + 2 + 1).factorial := by
          simp only [Nat.factorial_succ, show m + 2 + 1 = m + 3 by omega]

/-- Double factorial bound: (n-1)‼ ≤ n!^{1/2} for all n.
This converts the Wick bound into the OS1' factorial form. -/
theorem double_factorial_le_sqrt_factorial (n : ℕ) :
    ((n - 1).doubleFactorial : ℝ) ≤ (n.factorial : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow]
  rw [Real.le_sqrt (Nat.cast_nonneg _)]
  · have h : (n - 1).doubleFactorial ^ 2 ≤ n.factorial := by
      cases n with
      | zero => norm_num
      | succ n => exact dfact_sq_le_succ_fact n
    exact_mod_cast h
  · exact Nat.cast_nonneg _

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-- Wick bound in factorial form (suitable for OS1'):
  |E[∏ᵢ ω(fᵢ)]| ≤ n!^{1/2} · ∏ᵢ ‖T(fᵢ)‖ -/
theorem wick_bound_factorial (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n.factorial : ℝ) ^ ((1 : ℝ) / 2) * ∏ i, ‖T (f i)‖ :=
  calc ‖∫ ω, ∏ i, ω (f i) ∂(measure T)‖
      ≤ (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖ := wick_bound T n f
    _ ≤ (n.factorial : ℝ) ^ ((1 : ℝ) / 2) * ∏ i, ‖T (f i)‖ := by
        apply mul_le_mul_of_nonneg_right (double_factorial_le_sqrt_factorial n)
        exact Finset.prod_nonneg (fun i _ => norm_nonneg _)

end GaussianField
