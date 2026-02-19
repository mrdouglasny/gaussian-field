/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Textbook Axioms

Sorry'd lemmas corresponding to standard textbook results that are not yet
in Mathlib. Used as building blocks in the SchwartzNuclear proofs.

## Inventory

- `contDiff_schwartz_parametric_integral` — **Leibniz integral rule (C^∞)**
- `norm_iteratedFDeriv_iteratedFDeriv` — **Currying isometry for iterated derivatives**
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open MeasureTheory SchwartzMap
open scoped ContDiff

/-- **Textbook: Leibniz integral rule (C^∞, Schwartz integrand).**

Given a Schwartz function `f` on `E`, a Schwartz function `g` on `ℝ`, and
a parametric embedding `ι : H → ℝ → E`, if:
- for each `t`, `y ↦ ι(y,t)` is C^∞, and
- for each derivative order `m`, `‖D^m_y[f(ι(·,t))](y)‖` is uniformly bounded,

then `y ↦ ∫_t f(ι(y,t)) · g(t) dt` is C^∞ and `D^m` commutes with `∫`.

**Proof sketch**: Induction on `m` using `hasFDerivAt_integral_of_dominated_of_fderiv_le`.
The bound `‖D^m_y[f(ι(·,t))] · g(t)‖ ≤ C_m · |g(t)|` is integrable since `g` is Schwartz.

**Reference**: Folland, "Real Analysis", Theorem 2.27 (iterated version). -/
lemma contDiff_schwartz_parametric_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [FiniteDimensional ℝ E]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : SchwartzMap E ℝ) (g : SchwartzMap ℝ ℝ)
    (ι : H → ℝ → E)
    (hι_smooth : ∀ t, ContDiff ℝ ∞ (ι · t))
    (hι_bound : ∀ m : ℕ, ∃ C : ℝ, ∀ y t,
      ‖iteratedFDeriv ℝ m (fun y' => f (ι y' t)) y‖ ≤ C) :
    ContDiff ℝ ∞ (fun y => ∫ t, f (ι y t) * g t) ∧
    ∀ (m : ℕ) (y : H),
      iteratedFDeriv ℝ m (fun y' => ∫ t, f (ι y' t) * g t) y =
      ∫ t, iteratedFDeriv ℝ m (fun y' => f (ι y' t) * g t) y := by
  sorry

/-- **Textbook: Currying isometry for iterated Fréchet derivatives.**

`‖iteratedFDeriv n (iteratedFDeriv l' f) z‖ = ‖iteratedFDeriv (n + l') f z‖`

Follows by induction on `l'` using `iteratedFDeriv_succ_eq_comp_left`,
`LinearIsometryEquiv.norm_iteratedFDeriv_comp_left`, and `norm_iteratedFDeriv_fderiv`.
Mathematically trivial but sorry'd due to Lean type-checker timeout on
dependent `Fin` types in `whnf` (tested up to 3.2M heartbeats). -/
lemma norm_iteratedFDeriv_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n l' : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ l' f) z‖ =
      ‖iteratedFDeriv ℝ (n + l') f z‖ := by
  sorry
