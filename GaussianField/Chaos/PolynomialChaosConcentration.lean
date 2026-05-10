/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Polynomial Chaos Concentration (Janson Theorem 5.10)

For a centered $F \in \mathcal H^{\le d}$ (a polynomial of total
degree $\le d$ in a finite-dim Gaussian vector), there is a
universal constant $c_d > 0$ depending only on $d$ such that
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr),
\qquad \lambda > 0.
$$

The exponent $2/d$ is sharp (saturated by $F = \phi_1^d$). The
constant $c_d$ is dimension-independent (independent of $n$, the
size of the Gaussian vector).

## Equivalent Bonami-Nelson L^p form

$$
\|F\|_{L^p} \;\le\; (p - 1)^{d/2} \, \|F\|_{L^2},
\qquad p \ge 2.
$$

## Proof outline (three ingredients)

1. **OU hypercontractivity** restricted to chaos $\mathcal H_k$
   (`OUEigenfunctions`): for $f \in \mathcal H_k$ and $p \ge 2$,
   $\|f\|_{L^p} \le (p-1)^{k/2} \|f\|_{L^2}$.
2. **Markov / Chebyshev**: $\mathbb P(|F| > \lambda \|F\|_2) \le
   (\|F\|_p / (\lambda \|F\|_2))^p$.
3. **Optimize** $p$: set $p - 1 = (\lambda/e)^{2/d}$.

This file is the LD endpoint that downstream consumers call.

## Main theorems

- `bonami_nelson_chaos` — L^p improvement on a single chaos $\mathcal H_k$.
- `bonami_nelson_chaosLE` — L^p improvement on $\mathcal H^{\le d}$
  (with a multiplicative degree-dependent constant).
- `polynomial_chaos_concentration` — the Janson 5.10 tail bound.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 5.10
  (the gold-standard reference for this bound).
- A. Bonami, *Étude des coefficients de Fourier des fonctions de
  $L^p(G)$*, Ann. Inst. Fourier 20 (1970).
- E. Nelson, "The free Markov field," J. Funct. Anal. 12 (1973).
- R. Adamczak, P. Wolff, "Concentration inequalities for non-Lipschitz
  functions," Probab. Theory Related Fields 162 (2015) — modern
  treatment with explicit constants.

## Status

API + axiom skeleton (2026-05-08). The Bonami-Nelson L^p improvement
on a single chaos follows immediately from the OU eigenfunction
identity (`ouSemigroup_act_wienerChaos`) plus the abstract
hypercontractivity inequality already in
`Abstract/Hypercontractivity.lean`. The concentration tail bound is
a Markov + optimize derivation from the L^p bound. Both are stated
as axioms here pending the OU semigroup being concretely available;
the proof scripts are short once the prerequisites are wired.
-/

import GaussianField.Chaos.OUEigenfunctions
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section

namespace MeasureTheory.Lp

/-- The coercion `Lp E p μ → (α → E)` distributes over `Finset` sums almost
everywhere. Inductive bridge from `coeFn_zero` and `coeFn_add`; not currently
in Mathlib at v4.29.0. -/
theorem coeFn_finset_sum {α E ι : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup E] {p : ENNReal} [DecidableEq ι]
    (s : Finset ι) (f : ι → Lp E p μ) :
    ((∑ i ∈ s, f i : Lp E p μ) : α → E)
      =ᵐ[μ] ∑ i ∈ s, ((f i : Lp E p μ) : α → E) := by
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      exact Lp.coeFn_zero E p μ
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih]
        with x hx_add hx_ih
      simp only [Pi.add_apply, Finset.sum_apply] at hx_add hx_ih ⊢
      rw [hx_add, hx_ih]

end MeasureTheory.Lp

namespace GaussianField.Chaos

open MeasureTheory

variable {n : ℕ}

/-- **Bonami-Nelson L^p improvement on a single Wiener chaos.**

For $f \in \mathcal H_k$ and $p \ge 2$:
$$
\|f\|_{L^p} \;\le\; (p - 1)^{k/2} \, \|f\|_{L^2}.
$$

**Reference:** Bonami (1970) for the 1D case; Nelson (1973) for the
infinite-dim OU semigroup. Janson §5.1.

**Proof strategy:** The OU semigroup $T_t$ is hypercontractive: it
maps $L^2 \to L^p$ for $e^{2t} = p - 1$ with operator norm $\le 1$
(`Abstract/Hypercontractivity.lean`). Restricted to $\mathcal H_k$,
$T_t$ acts as multiplication by $e^{-kt}$
(`ouSemigroup_act_wienerChaos`), hence
$\|f\|_{L^p} \cdot e^{-kt} \le \|f\|_{L^2}$. Solving for
$\|f\|_{L^p}$ with $e^{2t} = p - 1$ gives the bound. -/
theorem bonami_nelson_chaos (n k : ℕ)
    (f : Lp ℝ 2 (stdGaussianFin n))
    (hf : f ∈ wienerChaos n k)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
      ENNReal.ofReal ((p - 1) ^ ((k : ℝ) / 2)) *
        eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
  -- Choose t = (1/2) log(p-1). With p ≥ 2 we get t ≥ 0 and e^{2t} = p - 1.
  set t : ℝ := (1 / 2) * Real.log (p - 1) with ht_def
  have hp1 : (1 : ℝ) ≤ p - 1 := by linarith
  have hp1_pos : (0 : ℝ) < p - 1 := by linarith
  have ht_nonneg : 0 ≤ t := by
    have hlog : 0 ≤ Real.log (p - 1) := Real.log_nonneg hp1
    rw [ht_def]; positivity
  have h_exp_2t : Real.exp (2 * t) = p - 1 := by
    have h2t : 2 * t = Real.log (p - 1) := by rw [ht_def]; ring
    rw [h2t, Real.exp_log hp1_pos]
  have h_nelson : p - 1 ≤ Real.exp (2 * t) := by rw [h_exp_2t]
  -- Apply OU hypercontractivity at this t.
  have h_hyper :=
    ouSemigroupAct_eLpNorm_hypercontractive p hp t ht_nonneg h_nelson f
  -- Identify T_t f = e^{-kt} • f using the chaos action axiom.
  have h_chaos := ouSemigroupAct_eq_smul_of_mem_wienerChaos k t ht_nonneg f hf
  -- Substitute: eLpNorm (T_t f) p ≤ eLpNorm f 2 becomes
  --             eLpNorm (e^{-kt} • f) p ≤ eLpNorm f 2.
  have h_coe :
      ((ouSemigroupAct n t f : Lp ℝ 2 (stdGaussianFin n)) :
        (Fin n → ℝ) → ℝ)
        =ᵐ[stdGaussianFin n]
          Real.exp (-(k : ℝ) * t) • ((f : (Fin n → ℝ) → ℝ)) := by
    have := Lp.coeFn_smul (Real.exp (-(k : ℝ) * t)) f
    have hsm : ((Real.exp (-(k : ℝ) * t) • f :
        Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
          =ᵐ[stdGaussianFin n]
            Real.exp (-(k : ℝ) * t) • ((f : (Fin n → ℝ) → ℝ)) := this
    have hcong : ouSemigroupAct n t f =
        Real.exp (-(k : ℝ) * t) • f := h_chaos
    exact hcong ▸ hsm
  rw [eLpNorm_congr_ae h_coe] at h_hyper
  rw [eLpNorm_const_smul] at h_hyper
  -- h_hyper : ‖e^{-kt}‖ₑ * eLpNorm f p ≤ eLpNorm f 2
  have h_exp_pos : 0 < Real.exp (-(k : ℝ) * t) := Real.exp_pos _
  have h_enorm : ‖Real.exp (-(k : ℝ) * t)‖ₑ =
      ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) := by
    rw [Real.enorm_eq_ofReal h_exp_pos.le]
  rw [h_enorm] at h_hyper
  -- Now we have ENNReal.ofReal e^{-kt} * eLpNorm f p ≤ eLpNorm f 2.
  -- Multiply both sides by ENNReal.ofReal e^{kt} and identify
  -- e^{kt} = (p-1)^{k/2}.
  have h_mul_inv : ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
      ENNReal.ofReal (Real.exp ((k : ℝ) * t)) = 1 := by
    rw [← ENNReal.ofReal_mul h_exp_pos.le, ← Real.exp_add]
    have : -(k : ℝ) * t + (k : ℝ) * t = 0 := by ring
    rw [this, Real.exp_zero, ENNReal.ofReal_one]
  have h_exp_kt_pos : 0 < Real.exp ((k : ℝ) * t) := Real.exp_pos _
  have h_step :
      eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n)
        ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
            eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
    have h_left :
        ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
          (ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
            eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n))
          = eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
              (stdGaussianFin n) := by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal _)
        (ENNReal.ofReal (Real.exp (-(k : ℝ) * t))), h_mul_inv, one_mul]
    calc eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n)
        = ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
            (ENNReal.ofReal (Real.exp (-(k : ℝ) * t)) *
              eLpNorm (f : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p)
                (stdGaussianFin n)) := h_left.symm
      _ ≤ ENNReal.ofReal (Real.exp ((k : ℝ) * t)) *
          eLpNorm (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
            exact mul_le_mul_right h_hyper
              (ENNReal.ofReal (Real.exp ((k : ℝ) * t)))
  -- Identify e^{kt} = (p-1)^{k/2} as nonneg reals.
  have h_kt_eq : Real.exp ((k : ℝ) * t) = (p - 1) ^ ((k : ℝ) / 2) := by
    have hkt : (k : ℝ) * t = Real.log (p - 1) * ((k : ℝ) / 2) := by
      rw [ht_def]; ring
    rw [hkt, ← Real.rpow_def_of_pos hp1_pos ((k : ℝ) / 2)]
  rw [h_kt_eq] at h_step
  exact h_step

/-- **Bonami-Nelson L^p improvement on $\mathcal H^{\le d}$.**

Triangle inequality across $k = 0, \dots, d$ extends the per-chaos
bound `bonami_nelson_chaos` to $\mathcal H^{\le d}$ at the cost of a
degree-$d$ prefactor:
$$
\|F\|_{L^p} \;\le\; (d + 1) \, (p - 1)^{d/2} \, \|F\|_{L^2}.
$$

(A sharper $\sqrt{d+1}$ factor is available via Cauchy–Schwarz on the
chaos decomposition + the `wienerChaos_orthogonal` Pythagoras; the
$(d+1)$ factor here is adequate for the downstream concentration
derivation.)

**Reference:** Janson §5.1.

**Proof strategy:**
1. Decompose `F = ∑_{k=0..d} f_k` with `f_k = chaosProjection n k F`
   via `chaosProjection_sum_eq_of_mem_wienerChaosLE`.
2. Triangle inequality on `eLpNorm` (`eLpNorm_sum_le`):
   `‖F‖_p ≤ ∑_k ‖f_k‖_p`.
3. Per-chaos `bonami_nelson_chaos` on each summand:
   `‖f_k‖_p ≤ (p-1)^{k/2} ‖f_k‖_2`.
4. Bound `(p-1)^{k/2} ≤ (p-1)^{d/2}` for `k ≤ d` (Real.rpow monotone
   in the exponent for `p-1 ≥ 1`).
5. `eLpNorm`-contractive `chaosProjection`
   (`chaosProjection_eLpNorm_two_le`):
   `‖f_k‖_2 ≤ ‖F‖_2` for each `k`.
6. Sum over `k = 0, …, d` (cardinality `d+1`):
   `∑_k (p-1)^{d/2} ‖f_k‖_2 ≤ (d+1) (p-1)^{d/2} ‖F‖_2`. -/
theorem bonami_nelson_chaosLE (n d : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n))
    (hF : F ∈ wienerChaosLE n d)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
      ENNReal.ofReal (((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) *
        eLpNorm (F : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := by
  set f : ℕ → Lp ℝ 2 (stdGaussianFin n) := fun k => chaosProjection n k F
    with hf_def
  have h_mem : ∀ k, f k ∈ wienerChaos n k :=
    fun k => chaosProjection_mem_wienerChaos n k F
  have h_decomp : F = ∑ k ∈ Finset.range (d + 1), f k :=
    chaosProjection_sum_eq_of_mem_wienerChaosLE n d F hF
  have h_contract : ∀ k,
      eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) ≤
        eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) :=
    fun k => chaosProjection_eLpNorm_two_le n k F
  have hp_minus_1_one_le : (1 : ℝ) ≤ p - 1 := by linarith
  have h_each : ∀ k ∈ Finset.range (d + 1),
      eLpNorm ((f k : (Fin n → ℝ) → ℝ)) (ENNReal.ofReal p) (stdGaussianFin n) ≤
        ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
          eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
    intro k hk
    have hk_le_d : (k : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h_kd : (p - 1) ^ ((k : ℝ) / 2) ≤ (p - 1) ^ ((d : ℝ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_le hp_minus_1_one_le
      linarith
    calc eLpNorm ((f k : (Fin n → ℝ) → ℝ))
            (ENNReal.ofReal p) (stdGaussianFin n)
        ≤ ENNReal.ofReal ((p - 1) ^ ((k : ℝ) / 2)) *
            eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) :=
          bonami_nelson_chaos n k (f k) (h_mem k) p hp
      _ ≤ ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
            eLpNorm ((f k : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by gcongr
      _ ≤ ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
            eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
            gcongr; exact h_contract k
  have h_card : (Finset.range (d + 1)).card = d + 1 := Finset.card_range _
  have h_meas : ∀ i ∈ Finset.range (d + 1),
      AEStronglyMeasurable ((f i : (Fin n → ℝ) → ℝ)) (stdGaussianFin n) :=
    fun i _ => Lp.aestronglyMeasurable _
  have hp_one : 1 ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h_coe_sum :
      ((F : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
        =ᵐ[stdGaussianFin n]
          ∑ k ∈ Finset.range (d + 1),
            ((f k : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ) := by
    rw [h_decomp]; exact Lp.coeFn_finset_sum _ _
  rw [eLpNorm_congr_ae h_coe_sum]
  refine (eLpNorm_sum_le h_meas hp_one).trans ?_
  refine (Finset.sum_le_card_nsmul (Finset.range (d + 1))
    (fun k => eLpNorm ((f k : (Fin n → ℝ) → ℝ))
      (ENNReal.ofReal p) (stdGaussianFin n))
    (ENNReal.ofReal ((p - 1) ^ ((d : ℝ) / 2)) *
      eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)) h_each).trans ?_
  rw [h_card, nsmul_eq_mul, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  have h_card_cast : ((d + 1 : ℕ) : ENNReal) = ENNReal.ofReal ((d : ℝ) + 1) := by
    rw [ENNReal.ofReal_add (by positivity) (by norm_num),
      ENNReal.ofReal_natCast, ENNReal.ofReal_one]
    push_cast; rfl
  rw [h_card_cast]
  rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]

private theorem eLpNorm_two_eq_ofReal_norm {n : ℕ}
    (F : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm (F : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) = ENNReal.ofReal ‖F‖ := by
  rw [Lp.norm_def]
  exact (ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)).symm

private theorem one_le_two_mul_exp_neg_half_ennreal {t : ℝ} (ht : t < 1) :
    (1 : ENNReal) ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) := by
  have hhalf_log_two : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have htlog : (1 / 2 : ℝ) * t < Real.log 2 := by
    have hhalf_t : (1 / 2 : ℝ) * t < 1 / 2 := by
      linarith
    exact lt_trans hhalf_t hhalf_log_two
  have hneg : -Real.log 2 < -((1 / 2 : ℝ) * t) := by
    linarith
  have hexp : Real.exp (-Real.log 2) < Real.exp (-((1 / 2 : ℝ) * t)) := by
    exact (Real.exp_lt_exp).2 hneg
  have hhalf : (1 / 2 : ℝ) < Real.exp (-((1 / 2 : ℝ) * t)) := by
    have hhalf_eq : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [← Real.log_inv]
      norm_num
      rw [Real.exp_log]
      norm_num
    rw [hhalf_eq] at hexp
    exact hexp
  have hreal : (1 : ℝ) ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
    have hmul : (1 : ℝ) < 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      have := mul_lt_mul_of_pos_left hhalf (show (0 : ℝ) < 2 by norm_num)
      simpa using this
    exact hmul.le
  rw [← ENNReal.ofReal_one, show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal hreal

private theorem exp_neg_one_add_le_two_mul_exp_neg_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(1 + t)) ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
  have hexp_one : Real.exp (-1 : ℝ) < 1 / 2 := Real.exp_neg_one_lt_half
  have hexp_t : Real.exp (-t) ≤ Real.exp (-(1 / 2 : ℝ) * t) := by
    apply (Real.exp_le_exp).2
    linarith
  calc
    Real.exp (-(1 + t)) = Real.exp (-1) * Real.exp (-t) := by
      rw [show -(1 + t) = -1 + -t by ring, Real.exp_add]
    _ ≤ (1 / 2) * Real.exp (-(1 / 2 : ℝ) * t) := by
      gcongr
    _ ≤ 2 * Real.exp (-(1 / 2 : ℝ) * t) := by
      have hpos : 0 < Real.exp (-(1 / 2 : ℝ) * t) := Real.exp_pos _
      nlinarith

private theorem markov_bonami_bound {n d : ℕ}
    (F : Lp ℝ 2 (stdGaussianFin n)) (hF : F ∈ wienerChaosLE n d)
    (lam p A : ℝ) (hlam : 0 < lam) (hFnorm : 0 < ‖F‖)
    (hA : A = ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)) (hp : 2 ≤ p) :
    (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
      ENNReal.ofReal ((A / lam) ^ p) := by
  have hp_nonneg : 0 ≤ p := by
    linarith
  have hp_ne_zero : ENNReal.ofReal p ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  have hp_ne_top : ENNReal.ofReal p ≠ ⊤ := by
    simp
  have hε_ne_zero : ENNReal.ofReal (lam * ‖F‖) ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hmarkov :
      (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
        (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p := by
    calc
      (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|}
        ≤ (stdGaussianFin n) {x | ENNReal.ofReal (lam * ‖F‖) ≤ ‖((F : (Fin n → ℝ) → ℝ) x)‖ₑ} := by
            refine measure_mono ?_
            intro x hx
            simp only [Set.mem_setOf_eq, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal hx.le
      _ ≤ (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p := by
            simpa [ENNReal.toReal_ofReal hp_nonneg] using
              (MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm (stdGaussianFin n)
                hp_ne_zero hp_ne_top (Lp.aestronglyMeasurable F) hε_ne_zero (by simp))
  have hbn := bonami_nelson_chaosLE n d F hF p hp
  have hconst_nonneg : 0 ≤ A := by
    rw [hA]
    have hp1 : 0 ≤ p - 1 := by
      linarith
    positivity
  have hbn' :
      eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ≤
        ENNReal.ofReal (A * ‖F‖) := by
    rw [← hA] at hbn
    rw [eLpNorm_two_eq_ofReal_norm F, ← ENNReal.ofReal_mul hconst_nonneg] at hbn
    simpa [mul_assoc] using hbn
  have htail :
      (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
        eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p ≤
      ENNReal.ofReal ((A / lam) ^ p) := by
    calc
      (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p *
          eLpNorm (F : (Fin n → ℝ) → ℝ) (ENNReal.ofReal p) (stdGaussianFin n) ^ p
        ≤ (ENNReal.ofReal (lam * ‖F‖))⁻¹ ^ p * (ENNReal.ofReal (A * ‖F‖)) ^ p := by
            gcongr
      _ = ENNReal.ofReal ((A / lam) ^ p) := by
        have hmul_pos : 0 < lam * ‖F‖ := mul_pos hlam hFnorm
        have hA_mul_nonneg : 0 ≤ A * ‖F‖ := mul_nonneg hconst_nonneg hFnorm.le
        have hinv_nonneg : 0 ≤ (lam * ‖F‖)⁻¹ := by positivity
        have hrpow_nonneg : 0 ≤ ((lam * ‖F‖)⁻¹) ^ p := by positivity
        rw [← ENNReal.ofReal_inv_of_pos hmul_pos,
          ENNReal.ofReal_rpow_of_nonneg hinv_nonneg hp_nonneg,
          ENNReal.ofReal_rpow_of_nonneg hA_mul_nonneg hp_nonneg,
          ← ENNReal.ofReal_mul hrpow_nonneg]
        congr 1
        rw [← Real.mul_rpow hinv_nonneg hA_mul_nonneg]
        congr 1
        have hcancel : lam * ‖F‖ ≠ 0 := by positivity
        field_simp [hcancel]
  exact hmarkov.trans htail

/-- **Polynomial Chaos Concentration (Janson Theorem 5.10).**

For centered $F \in \mathcal H^{\le d}$ with $d \ge 1$, there is a
universal constant $c_d > 0$ (depending only on $d$, not on $n$ or
the specific Gaussian vector) such that for all $\lambda > 0$,
$$
\mathbb P\bigl(|F| > \lambda \, \|F\|_{L^2}\bigr)
  \;\le\; 2 \exp\bigl(-c_d \, \lambda^{2/d}\bigr).
$$

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 5.10.

**Discharge plan** (Gemini deep-think, 2026-05-08; standard textbook
calculus, ~50–150 lines of Lean once attempted):

*Explicit constant:*
`c_d := (1/2) * (1 / (Real.exp 1 * (d + 1))) ^ (2 / d)`.

*Threshold:*
`L0 := Real.exp 1 * (d + 1)`.

*Proof sketch:* Reduce to `‖F‖_2 = 1` (the inequality is homogeneous
in `F` once we divide by `‖F‖_2`; the `‖F‖_2 = 0` case has empty
event LHS = 0). Case-split on `λ`:

* **`λ ≥ L0` (large `λ`).** Set `p := 1 + (λ / L0)^(2/d)`. Then
  `p ≥ 2` (since `λ/L0 ≥ 1` and `2/d > 0`).
  - Markov (`MeasureTheory.meas_ge_le_mul_pow_eLpNorm_enorm`):
    `μ {|F| > λ} ≤ ‖F‖_p^p / λ^p`.
  - `bonami_nelson_chaosLE` at this `p`:
    `‖F‖_p ≤ (d+1)(p-1)^{d/2} = (d+1) · (λ/L0)`
    (the algebra: `(p-1)^{d/2} = ((λ/L0)^{2/d})^{d/2} = λ/L0`).
  - So `((d+1)(p-1)^{d/2})/λ = (d+1)/L0 = 1/Real.exp 1`,
    and the bound becomes `(1/e)^p = exp(-p)
    = exp(-(1 + (λ/L0)^{2/d})) = exp(-1) · exp(-(λ/L0)^{2/d})`.
  - Compare to target `2 · exp(-c_d λ^{2/d})`: with `c_d = (1/2) L0^{-2/d}`
    and `(λ/L0)^{2/d} = λ^{2/d} · L0^{-2/d}`, this reduces to
    `1/(2e) ≤ exp((1/2)(λ/L0)^{2/d})`, which holds since
    `(λ/L0)^{2/d} ≥ 1` and `1 ≤ 2 e^{3/2}` (a `nlinarith`/`norm_num`
    check).

* **`0 < λ < L0` (small `λ`).** The bound `μ {|F| > λ‖F‖_2} ≤ 1` is
  trivial (probability measure). Suffices to show
  `1 ≤ 2 · exp(-c_d λ^{2/d})`, i.e., `c_d λ^{2/d} ≤ log 2`.
  - With `c_d = (1/2) L0^{-2/d}` and `λ < L0`, the LHS is
    `(1/2) (λ/L0)^{2/d} < 1/2`.
  - And `1/2 < log 2 ≈ 0.693…`, a `Real.log_two_gt_d9`-style fact.

The combined bound holds with this single `c_d`. The optimization
choice for `p` is the standard Janson recipe; the algebraic
identification `(p-1)^{d/2} = λ/L0` is the slickness that makes the
exponential exactly `(1/e)^p`. The proof below follows this plan. -/
theorem polynomial_chaos_concentration (n d : ℕ) (hd : 1 ≤ d) :
    ∃ c_d : ℝ, 0 < c_d ∧
      ∀ (F : Lp ℝ 2 (stdGaussianFin n)),
        F ∈ wienerChaosLE n d →
        ∀ (lam : ℝ), 0 < lam →
          (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
            2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d))) := by
  let L0 : ℝ := Real.exp 1 * ((d : ℝ) + 1)
  let c_d : ℝ := (1 / 2) * (1 / L0) ^ ((2 : ℝ) / d)
  refine ⟨c_d, ?_, ?_⟩
  · dsimp [c_d, L0]
    positivity
  · intro F hF lam hlam
    have hd_pos : (0 : ℝ) < d := by
      exact_mod_cast (lt_of_lt_of_le zero_lt_one hd)
    have hd_ne : (d : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one hd))
    have hL0_pos : 0 < L0 := by
      dsimp [L0]
      positivity
    by_cases hnorm_zero : ‖F‖ = 0
    · have hF_zero : F = 0 :=
        (MeasureTheory.Lp.norm_eq_zero_iff (by positivity : (0 : ENNReal) < 2)).1 hnorm_zero
      cases hF_zero
      have hzero :
          (stdGaussianFin n)
            {x | lam * ‖(0 : Lp ℝ 2 (stdGaussianFin n))‖ <
              |((0 : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ) x|} = 0 := by
        rw [show ‖(0 : Lp ℝ 2 (stdGaussianFin n))‖ = 0 by simp, mul_zero]
        refine measure_mono_null ?_ (ae_iff.mp (Lp.coeFn_zero ℝ 2 (stdGaussianFin n)))
        intro x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        exact abs_pos.mp hx
      rw [hzero]
      exact bot_le
    · have hFnorm : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnorm_zero)
      by_cases hlarge : L0 ≤ lam
      · set t : ℝ := (lam / L0) ^ ((2 : ℝ) / d)
        set p : ℝ := 1 + t
        have hratio_one : 1 ≤ lam / L0 := by
          rw [le_div_iff₀ hL0_pos]
          simpa using hlarge
        have hp_two_le : 2 ≤ p := by
          have ht_one : 1 ≤ t := by
            calc
              (1 : ℝ) = 1 ^ ((2 : ℝ) / d) := by simp
              _ ≤ (lam / L0) ^ ((2 : ℝ) / d) :=
                Real.rpow_le_rpow zero_le_one hratio_one (by positivity)
          linarith
        let A : ℝ := ((d : ℝ) + 1) * (p - 1) ^ ((d : ℝ) / 2)
        have htail :=
          markov_bonami_bound F hF lam p A hlam hFnorm rfl hp_two_le
        have hpminus :
            (p - 1) ^ ((d : ℝ) / 2) = lam / L0 := by
          dsimp [p, t]
          have hbase : 0 ≤ lam / L0 := by positivity
          have hsimp : 1 + (lam / L0) ^ ((2 : ℝ) / d) - 1 = (lam / L0) ^ ((2 : ℝ) / d) := by
            ring
          rw [hsimp, ← Real.rpow_mul hbase]
          have hm : ((2 : ℝ) / d) * ((d : ℝ) / 2) = 1 := by
            field_simp [hd_ne]
          rw [hm, Real.rpow_one]
        have hA_over_lam : A / lam = Real.exp (-1) := by
          dsimp [A]
          rw [hpminus]
          calc
            (((d : ℝ) + 1) * (lam / L0)) / lam = ((d : ℝ) + 1) / L0 := by
              field_simp [hlam.ne']
            _ = ((d : ℝ) + 1) / (Real.exp 1 * ((d : ℝ) + 1)) := by
              rfl
            _ = Real.exp (-1) := by
              calc
                ((d : ℝ) + 1) / (Real.exp 1 * ((d : ℝ) + 1)) = (Real.exp 1)⁻¹ := by
                  field_simp [hL0_pos.ne']
                _ = Real.exp (-1) := by
                  rw [Real.exp_neg]
        have hpow_exp : (A / lam) ^ p = Real.exp (-p) := by
          rw [hA_over_lam]
          calc
            (Real.exp (-1)) ^ p = Real.exp ((-1) * p) := by rw [← Real.exp_mul]
            _ = Real.exp (-p) := by congr 1; ring
        have hc_half :
            c_d * lam ^ ((2 : ℝ) / d) = t / 2 := by
          dsimp [c_d, L0, t]
          have hlam_nonneg : 0 ≤ lam := hlam.le
          have hinv_nonneg : 0 ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by positivity
          rw [mul_assoc, ← Real.mul_rpow hinv_nonneg hlam_nonneg]
          have hrewrite :
              (1 / (Real.exp 1 * ((d : ℝ) + 1))) * lam = lam / (Real.exp 1 * ((d : ℝ) + 1)) := by
            field_simp
          rw [hrewrite]
          ring
        have ht_ge_one : 1 ≤ t := by
          calc
            (1 : ℝ) = 1 ^ ((2 : ℝ) / d) := by simp
            _ ≤ (lam / L0) ^ ((2 : ℝ) / d) :=
              Real.rpow_le_rpow zero_le_one hratio_one (by positivity)
        have hreal :
            Real.exp (-p) ≤ 2 * Real.exp (-c_d * lam ^ ((2 : ℝ) / d)) := by
          have hp_neg : -p = -(1 + t) := by
            dsimp [p]
          rw [hp_neg]
          have haux := exp_neg_one_add_le_two_mul_exp_neg_half ht_ge_one
          have haux' : Real.exp (-t + -1) ≤ 2 * Real.exp (-(t / 2 : ℝ)) := by
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux
          have hc_neg : -c_d * lam ^ ((2 : ℝ) / d) = -(t / 2 : ℝ) := by
            linarith [hc_half]
          simpa [show -(1 + t) = -t + -1 by ring, hc_neg] using haux'
        have henn :
            ENNReal.ofReal (Real.exp (-p)) ≤
              2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d))) := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by norm_num,
            ← ENNReal.ofReal_mul' (Real.exp_pos _).le]
          exact ENNReal.ofReal_le_ofReal hreal
        have htail_exp :
            (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤
              ENNReal.ofReal (Real.exp (-p)) := by
          simpa [hpow_exp] using htail
        exact htail_exp.trans henn
      · have hsmall : lam < L0 := lt_of_not_ge hlarge
        set t : ℝ := (lam / L0) ^ ((2 : ℝ) / d)
        letI : IsProbabilityMeasure (stdGaussianFin n) := by
          refine ⟨?_⟩
          simp [stdGaussianFin]
        have ht_lt_one : t < 1 := by
          dsimp [t]
          have hratio : lam / L0 < 1 := by
            rw [div_lt_iff₀ hL0_pos]
            simpa using hsmall
          have hratio_nonneg : 0 ≤ lam / L0 := by positivity
          calc
            (lam / L0) ^ ((2 : ℝ) / d) < 1 ^ ((2 : ℝ) / d) :=
              Real.rpow_lt_rpow hratio_nonneg hratio (by positivity)
            _ = 1 := by simp
        have htriv :
            (stdGaussianFin n) {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|} ≤ 1 :=
          prob_le_one (μ := stdGaussianFin n)
            (s := {x | lam * ‖F‖ < |(F : (Fin n → ℝ) → ℝ) x|})
        have hsmall_bound :
            (1 : ENNReal) ≤ 2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) :=
          one_le_two_mul_exp_neg_half_ennreal ht_lt_one
        have hc_half :
            c_d * lam ^ ((2 : ℝ) / d) = t / 2 := by
          dsimp [c_d, L0, t]
          have hlam_nonneg : 0 ≤ lam := hlam.le
          have hinv_nonneg : 0 ≤ 1 / (Real.exp 1 * ((d : ℝ) + 1)) := by positivity
          rw [mul_assoc, ← Real.mul_rpow hinv_nonneg hlam_nonneg]
          have hrewrite :
              (1 / (Real.exp 1 * ((d : ℝ) + 1))) * lam = lam / (Real.exp 1 * ((d : ℝ) + 1)) := by
            field_simp
          rw [hrewrite]
          ring
        have hrewrite_rhs :
            2 * ENNReal.ofReal (Real.exp (-(1 / 2 : ℝ) * t)) =
              2 * ENNReal.ofReal (Real.exp (-c_d * lam ^ ((2 : ℝ) / d))) := by
          congr 2
          congr 1
          linarith [hc_half]
        exact htriv.trans (hsmall_bound.trans_eq hrewrite_rhs)

end GaussianField.Chaos
