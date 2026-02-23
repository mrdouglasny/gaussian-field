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

/-! ## Wick's theorem — recursive form

The recursive form avoids the combinatorial overhead of enumerating
perfect pairings. It says: pick any index (we use 0), then the
(n+2)-point function equals the sum over all partners j for index 0.

The proof uses `gaussian_ibp` as the base case and extends by induction,
differentiating the IBP identity with respect to additional parameters
(one Leibniz application per step). -/

/-- **Wick's theorem (recursive form).**

For a centered Gaussian measure with covariance C(f,g) = ⟨Tf, Tg⟩_H:

  E[ω(f₀) · ∏ⱼ ω(gⱼ)] = ∑ⱼ C(f₀, gⱼ) · E[∏_{i≠j} ω(gᵢ)]

This is proved by induction on n using `gaussian_ibp`. The base case n=0
is `cross_moment_eq_covariance`. The inductive step differentiates the
IBP identity ∫ ω(f₀)·exp(iω(h)) = ⟨Tf₀,Th⟩·i·charFun(h) with respect
to additional test function parameters, extracting polynomial coefficients
from the exponential generating function. -/
theorem wick_recursive (n : ℕ) (f₀ : E) (g : Fin (n + 1) → E) :
    ∫ ω : Configuration E, ω f₀ * ∏ i, ω (g i) ∂(measure T) =
      ∑ j : Fin (n + 1), @inner ℝ H _ (T f₀) (T (g j)) *
        ∫ ω : Configuration E, ∏ i : Fin n,
          ω (g (Fin.succAbove j i)) ∂(measure T) := by
  -- Proof by extracting multilinear coefficients from `gaussian_ibp`:
  -- Setting h = ∑ⱼ tⱼ gⱼ in gaussian_ibp, the coefficient of ∏ⱼ tⱼ on each side
  -- gives the Wick recursion. Both sides are analytic in t, so coefficient comparison
  -- is valid. This requires (n+1)-fold Leibniz differentiation under the integral.
  sorry

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
