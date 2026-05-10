/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Polynomials Are OU Eigenfunctions

The Ornstein-Uhlenbeck generator on $L^2(\gamma_n)$ (with $\gamma_n$
the standard multivariate Gaussian on $\mathbb R^n$) is
$$
L f(x) \;=\; \Delta f(x) - x \cdot \nabla f(x).
$$

The key spectral fact: $L H_\alpha = -|\alpha| H_\alpha$ for every
multi-index $\alpha$, so the $k$-th Wiener chaos is the eigenspace
of $L$ with eigenvalue $-k$. The OU semigroup $T_t$ acts on
$\mathcal H_k$ by $e^{-kt}$.

The proof is direct algebra:
1. The 1D recurrence gives $L_1 H_k = -k \, H_k$ where
   $L_1 = \partial_x^2 - x \partial_x$.
2. The multi-dim $L$ is a sum of single-coordinate operators
   $L_i = \partial_{x_i}^2 - x_i \partial_{x_i}$.
3. $H_\alpha = \prod_i H_{\alpha_i}(x_i)$, and each $L_i$ acts only
   on its own coordinate, contributing $-\alpha_i$. Sum gives
   $-|\alpha|$.

This bypasses any infinite-dimensional spectral theory: the
eigenfunction relation is a polynomial identity.

## Main definitions

- `ouGenerator n` — the operator $L = \Delta - x \cdot \nabla$ on
  smooth functions $\mathbb R^n \to \mathbb R$.

## Main theorems

- `ouGenerator_hermiteMulti_1d` — `L₁ H_k = -k · H_k` (1D base case).
- `ouGenerator_hermiteMulti` — `L H_α = -|α| · H_α` (multi-index).
- `ouSemigroup_act_wienerChaos` — `T_t f = exp(-k t) · f` for
  `f ∈ wienerChaos γ k`. This is the semigroup-level reformulation.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §2.4
  (the OU semigroup) and Theorem 4.4 (eigenvalues of `L`).
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov
  Diffusion Operators*, Springer (2014), §2.7.

## Status

API + axiom skeleton (2026-05-08). The 1D and multivariate
eigenfunction identities are stated as axioms with explicit
proof-strategy docstrings citing the polynomial recurrence; the
semigroup-level reformulation depends on the
`Diffusion/OrnsteinUhlenbeck.lean` skeleton being filled in.
-/

import GaussianField.Chaos.WienerChaos
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section

namespace GaussianField.Chaos

/-- The 1D Ornstein-Uhlenbeck generator
$L_1 f(x) = f''(x) - x \, f'(x)$ acting on smooth real functions. -/
noncomputable def ouGenerator1D (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - x * deriv f x

/-- The $n$-dim Ornstein-Uhlenbeck generator
$L f(x) = \Delta f(x) - x \cdot \nabla f(x)$. -/
noncomputable def ouGenerator (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x =>
    (∑ i, fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single i 1)) -
    (∑ i, x i * fderiv ℝ f x (Pi.single i 1))

/-- The 1D Hermite polynomial as an `ℝ[X]` polynomial. Wrapper around
`(Polynomial.hermite k).map (Int.castRingHom ℝ)` matching gaussian-field's
`hermiteR k` so we can reuse `Polynomial.deriv_aeval` and the
`hermite_derivative` recurrence. -/
private noncomputable abbrev hermitePolyR (k : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite k).map (Int.castRingHom ℝ)

private lemma hermitePolyR_eval_eq_hermiteEval (k : ℕ) (x : ℝ) :
    (hermitePolyR k).eval x = hermiteEval k x := rfl

private lemma derivative_hermitePolyR (k : ℕ) :
    Polynomial.derivative (hermitePolyR (k + 1)) =
      ((k + 1 : ℕ) : Polynomial ℝ) * hermitePolyR k := by
  simp only [hermitePolyR]
  rw [Polynomial.derivative_map, hermite_derivative,
      Polynomial.map_mul, Polynomial.map_natCast]

/-- Derivative of `hermiteEval (k+1)` is `(k+1) · hermiteEval k`. -/
private lemma deriv_hermiteEval_succ (k : ℕ) (x : ℝ) :
    deriv (hermiteEval (k + 1)) x = (k + 1 : ℝ) * hermiteEval k x := by
  -- deriv (eval (hermite (k+1))) = eval (derivative (hermite (k+1)))
  -- = eval ((k+1) * hermite k) = (k+1) * hermiteEval k
  have h_aeval : deriv (fun u : ℝ => (hermitePolyR (k + 1)).eval u) x =
      (Polynomial.derivative (hermitePolyR (k + 1))).eval x := by
    have h1 : (fun u : ℝ => (hermitePolyR (k + 1)).eval u) =
        fun u : ℝ => Polynomial.aeval u (hermitePolyR (k + 1)) := by
      ext u
      simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
    rw [h1, Polynomial.deriv_aeval]
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
  show deriv (fun u : ℝ => (hermitePolyR (k + 1)).eval u) x = _
  rw [h_aeval, derivative_hermitePolyR, Polynomial.eval_mul, Polynomial.eval_natCast]
  push_cast
  rfl

/-- Hermite three-term recurrence at the value level:
`hermiteEval (k + 2) x = x · hermiteEval (k + 1) x − (k + 1) · hermiteEval k x`. -/
private lemma hermiteEval_recurrence (k : ℕ) (x : ℝ) :
    hermiteEval (k + 2) x =
      x * hermiteEval (k + 1) x - ((k + 1 : ℕ) : ℝ) * hermiteEval k x := by
  -- `hermite (k+2) = X * hermite (k+1) - derivative (hermite (k+1))`
  -- and `derivative (hermite (k+1)) = (k+1) * hermite k`.
  show (hermitePolyR (k + 2)).eval x =
    x * (hermitePolyR (k + 1)).eval x - ((k + 1 : ℕ) : ℝ) * (hermitePolyR k).eval x
  have h1 : hermitePolyR (k + 2) =
      Polynomial.X * hermitePolyR (k + 1) -
        Polynomial.derivative (hermitePolyR (k + 1)) := by
    simp only [hermitePolyR]
    rw [Polynomial.hermite_succ, Polynomial.map_sub, Polynomial.map_mul,
      Polynomial.map_X, Polynomial.derivative_map]
  rw [h1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
      derivative_hermitePolyR, Polynomial.eval_mul, Polynomial.eval_natCast]

/-- `hermiteEval` is differentiable on ℝ (as a polynomial evaluation). -/
private lemma hermiteEval_differentiable (k : ℕ) :
    Differentiable ℝ (hermiteEval k) := by
  show Differentiable ℝ (fun u : ℝ => (hermitePolyR k).eval u)
  exact (hermitePolyR k).differentiable

/-- **1D Hermite polynomials are OU eigenfunctions:** `L₁ H_k = −k · H_k`.

**Proof:** From `H_k'(x) = k · H_{k-1}(x)` (`deriv_hermiteEval_succ`) and the
three-term recurrence `H_{k+2}(x) = x H_{k+1}(x) − (k+1) H_k(x)`
(`hermiteEval_recurrence`), expand `L₁ H_k = H_k'' - x · H_k'`
and collapse via the recurrence.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4. -/
theorem ouGenerator1D_hermiteEval (k : ℕ) (x : ℝ) :
    ouGenerator1D (hermiteEval k) x = -(k : ℝ) * hermiteEval k x := by
  unfold ouGenerator1D
  match k with
  | 0 =>
    -- hermiteEval 0 = (fun _ => 1), so all derivatives vanish.
    have h_const : hermiteEval 0 = fun _ : ℝ => (1 : ℝ) := by
      funext y
      show (hermitePolyR 0).eval y = 1
      simp [hermitePolyR, Polynomial.hermite_zero]
    rw [h_const]
    simp
  | 0 + 1 =>
    -- hermiteEval 1 = id, deriv = 1, deriv² = 0; goal: 0 - x · 1 = -1 · x
    have h_id : hermiteEval 1 = fun y : ℝ => y := by
      funext y
      show (hermitePolyR 1).eval y = y
      simp [hermitePolyR, Polynomial.hermite_succ, Polynomial.hermite_zero]
    rw [h_id]
    simp
  | m + 1 + 1 =>
    -- f' = (m+2) · hermiteEval (m+1)
    have h_d1 : deriv (hermiteEval (m + 2)) = fun y => ((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) y := by
      funext y
      have := deriv_hermiteEval_succ (m + 1) y
      convert this using 1
      push_cast; ring
    rw [h_d1]
    -- f'' = (m+2) · deriv (hermiteEval (m+1)) = (m+2)(m+1) hermiteEval m
    have h_d2 : deriv (fun y => ((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) y) x =
        ((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * hermiteEval m x) := by
      rw [deriv_const_mul _ ((hermiteEval_differentiable (m + 1)).differentiableAt)]
      rw [deriv_hermiteEval_succ]
      push_cast; ring
    rw [h_d2]
    -- Goal: (m+2)(m+1) H_m x − x · (m+2) · H_{m+1} x = -(m+2) · H_{m+2} x
    -- Use H_{m+2} x = x · H_{m+1} x − (m+1) · H_m x.
    have h_rec := hermiteEval_recurrence m x
    -- Normalise `m+1+1` to `m+2` and push casts.
    show ((m + 2 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) * hermiteEval m x) -
        x * (((m + 2 : ℕ) : ℝ) * hermiteEval (m + 1) x) =
      -((m + 2 : ℕ) : ℝ) * hermiteEval (m + 2) x
    push_cast at h_rec ⊢
    linear_combination ((m : ℝ) + 2) * h_rec

/-! ## Multivariate slicing helpers (toward `ouGenerator_hermiteMultiEval`)

The OU generator definition uses `fderiv` on `(Fin n → ℝ) → ℝ`. To
reduce to the 1D case, slice along each coordinate: for fixed `x` and
`i`, the slice `s ↦ hermiteMultiEval α (Function.update x i s)` equals
`(∏_{j ≠ i} H_{α_j}(x_j)) · hermiteEval (α i) s`, and its
1D `ouGenerator1D` is computed by `ouGenerator1D_hermiteEval` times the
constant `∏_{j ≠ i} H_{α_j}(x_j)`. -/

/-- The "co-product" excluding coordinate `i`. -/
private noncomputable def hermiteMultiCoprod {n : ℕ} (α : Fin n → ℕ)
    (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  ∏ j ∈ (Finset.univ.erase i), hermiteEval (α j) (x j)

/-- The slice `s ↦ hermiteMultiEval α (update x i s)` equals
`(∏_{j ≠ i} H_{α_j}(x_j)) · hermiteEval (α i) s`. -/
private lemma hermiteMultiEval_update {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    hermiteMultiEval α (Function.update x i s) =
      hermiteMultiCoprod α i x * hermiteEval (α i) s := by
  unfold hermiteMultiEval hermiteMultiCoprod
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j => hermiteEval (α j) ((Function.update x i s) j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [Function.update_of_ne hj']

/-- Slice has a 1D derivative. -/
private lemma hermiteMultiEval_slice_HasDerivAt {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    HasDerivAt (fun t : ℝ => hermiteMultiEval α (Function.update x i t))
      (hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s) s := by
  -- Slice equals const · hermiteEval (α i) (·).
  have h_eq : (fun t : ℝ => hermiteMultiEval α (Function.update x i t)) =
      fun t => hermiteMultiCoprod α i x * hermiteEval (α i) t := by
    funext t
    exact hermiteMultiEval_update α x i t
  rw [h_eq]
  exact (hermiteEval_differentiable (α i)).differentiableAt.hasDerivAt.const_mul
    (hermiteMultiCoprod α i x)

/-- Helper: a Finset-product of `C^∞` functions of the form
`x ↦ p_j (x j)` is `C^∞`. -/
private lemma hermiteMultiProd_contDiff {n : ℕ} (α : Fin n → ℕ)
    (t : Finset (Fin n)) :
    ContDiff ℝ ⊤ (fun x : Fin n → ℝ => ∏ j ∈ t, hermiteEval (α j) (x j)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact contDiff_const
  | insert k s hk ih =>
    have h_eq : (fun x : Fin n → ℝ => ∏ j ∈ insert k s, hermiteEval (α j) (x j)) =
        fun x => hermiteEval (α k) (x k) * ∏ j ∈ s, hermiteEval (α j) (x j) := by
      funext x
      exact Finset.prod_insert hk
    rw [h_eq]
    refine ContDiff.mul ?_ ih
    -- hermiteEval (α k) (x k) = (hermitePolyR (α k)).eval (x k) = aeval (x k) (hermitePolyR (α k))
    -- composed with the projection x ↦ x k
    have h_one : ContDiff ℝ ⊤ (fun y : ℝ => (hermitePolyR (α k)).eval y) := by
      have : (fun y : ℝ => (hermitePolyR (α k)).eval y) =
          fun y : ℝ => Polynomial.aeval y (hermitePolyR (α k)) := by
        funext y
        simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_id]
      rw [this]
      exact Polynomial.contDiff_aeval (hermitePolyR (α k)) ⊤
    exact h_one.comp (contDiff_apply ℝ ℝ k)

/-- `hermiteMultiEval α` is `C^∞`, hence smooth. -/
private lemma hermiteMultiEval_contDiff {n : ℕ} (α : Fin n → ℕ) :
    ContDiff ℝ ⊤ (hermiteMultiEval α) := by
  unfold hermiteMultiEval
  exact hermiteMultiProd_contDiff α Finset.univ

/-- `hermiteMultiEval α` is differentiable at every point. -/
private lemma hermiteMultiEval_differentiable {n : ℕ} (α : Fin n → ℕ) :
    Differentiable ℝ (hermiteMultiEval α) :=
  (hermiteMultiEval_contDiff α).differentiable (by norm_num)

private lemma hermiteMultiEval_differentiableAt {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ (hermiteMultiEval α) x :=
  (hermiteMultiEval_differentiable α).differentiableAt

/-- Connect the slice derivative to the partial derivative `fderiv … (Pi.single i 1)`. -/
private lemma fderiv_hermiteMultiEval_apply_single {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i) := by
  -- The slice `s ↦ f (update x i s)` has derivative
  -- `fderiv f (update x i s) (Pi.single i 1)` by chain rule, then equals
  -- the slice's 1D derivative by `hermiteMultiEval_slice_HasDerivAt`.
  have h_slice := hermiteMultiEval_slice_HasDerivAt α x i (x i)
  have h_chain : HasDerivAt
      (fun s : ℝ => hermiteMultiEval α (Function.update x i s))
      (fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1)) (x i) := by
    have h_update := hasDerivAt_update x i (x i)
    have h_f : HasFDerivAt (hermiteMultiEval α)
        (fderiv ℝ (hermiteMultiEval α) x) x :=
      (hermiteMultiEval_differentiableAt α x).hasFDerivAt
    have h_eq : x = Function.update x i (x i) := (Function.update_eq_self i x).symm
    exact HasFDerivAt.comp_hasDerivAt_of_eq (x := x i) (l := hermiteMultiEval α)
      (l' := fderiv ℝ (hermiteMultiEval α) x) (y := x)
      (f := Function.update x i) (f' := Pi.single i 1)
      h_f h_update h_eq
  exact h_chain.unique h_slice

/-- The function `y ↦ fderiv f y (Pi.single i 1)` (the i-th partial derivative
as a function of the base point) coincides on the i-line through x with
`s ↦ c · deriv (hermiteEval (α i)) s` where `c = hermiteMultiCoprod α i x`. -/
private lemma fderiv_apply_single_update {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) (s : ℝ) :
    fderiv ℝ (hermiteMultiEval α) (Function.update x i s) (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s := by
  rw [fderiv_hermiteMultiEval_apply_single α (Function.update x i s) i]
  -- Need: `hermiteMultiCoprod α i (update x i s) = hermiteMultiCoprod α i x`
  -- and `(update x i s) i = s`.
  congr 1
  · unfold hermiteMultiCoprod
    refine Finset.prod_congr rfl ?_
    intro j hj
    have hj' : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update_of_ne hj']
  · rw [Function.update_self]

/-- `deriv` of `hermiteEval k` is differentiable. (Used for the second slice
derivative.) -/
private lemma deriv_hermiteEval_differentiable (k : ℕ) :
    Differentiable ℝ (deriv (hermiteEval k)) := by
  match k with
  | 0 =>
    have h : deriv (hermiteEval 0) = fun _ : ℝ => (0 : ℝ) := by
      have h_const : hermiteEval 0 = fun _ : ℝ => (1 : ℝ) := by
        funext y; show (hermitePolyR 0).eval y = 1
        simp [hermitePolyR, Polynomial.hermite_zero]
      funext y
      rw [h_const]; exact deriv_const y 1
    rw [h]; exact differentiable_const 0
  | k + 1 =>
    have h : deriv (hermiteEval (k + 1)) = fun y => ((k + 1 : ℕ) : ℝ) * hermiteEval k y := by
      funext y
      simpa using deriv_hermiteEval_succ k y
    rw [h]; exact (hermiteEval_differentiable k).const_mul _

/-- Second slice derivative: the slice `s ↦ fderiv f (update x i s) (Pi.single i 1)`
has 1D derivative `c · deriv²(hermiteEval (α i)) (x i)` at `s = x i`. -/
private lemma fderiv_apply_single_slice_HasDerivAt {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun s : ℝ => fderiv ℝ (hermiteMultiEval α) (Function.update x i s)
        (Pi.single i 1))
      (hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i))
      (x i) := by
  have h_eq : (fun s : ℝ => fderiv ℝ (hermiteMultiEval α) (Function.update x i s)
        (Pi.single i 1)) =
      fun s => hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) s := by
    funext s
    exact fderiv_apply_single_update α x i s
  rw [h_eq]
  exact (deriv_hermiteEval_differentiable (α i)).differentiableAt.hasDerivAt.const_mul
    (hermiteMultiCoprod α i x)

-- (`hermiteMultiEval_contDiff` defined above.)

/-- Connect the second slice derivative to `fderiv (fderiv f) x v w`. -/
private lemma fderiv_fderiv_apply_single_single {n : ℕ}
    (α : Fin n → ℕ) (x : Fin n → ℝ) (i : Fin n) :
    fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) =
      hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) := by
  -- Strategy: T = (· at Pi.single i 1) is a CLM. Apply chain rule:
  -- `g(y) := fderiv f y (Pi.single i 1) = T (fderiv f y)`. So
  -- `fderiv g x v = T (fderiv (fderiv f) x v)`.
  -- The slice 1D derivative of g at x_i along Function.update equals `fderiv g x (Pi.single i 1)`.
  -- And the slice equals the explicit derivative by `fderiv_apply_single_slice_HasDerivAt`.
  set T : ((Fin n → ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ (Pi.single i (1 : ℝ))
  set g : (Fin n → ℝ) → ℝ := fun y => fderiv ℝ (hermiteMultiEval α) y (Pi.single i 1)
  -- g = T ∘ fderiv (hermiteMultiEval α)
  have h_g : g = fun y => T (fderiv ℝ (hermiteMultiEval α) y) := by
    funext y
    rfl
  -- f is C^2
  have h_f_top : ContDiff ℝ ⊤ (hermiteMultiEval α) := hermiteMultiEval_contDiff α
  have h_fderiv_c1 : ContDiff ℝ 1 (fderiv ℝ (hermiteMultiEval α)) :=
    h_f_top.fderiv_right (le_top)
  have h_fderiv_diff : DifferentiableAt ℝ (fderiv ℝ (hermiteMultiEval α)) x :=
    (h_fderiv_c1.differentiable (by norm_num)).differentiableAt
  -- fderiv g x = T ∘ fderiv (fderiv f) x.
  have h_fderiv_g : fderiv ℝ g x = T.comp (fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x) := by
    rw [h_g]
    exact (T.hasFDerivAt.comp x h_fderiv_diff.hasFDerivAt).fderiv
  -- Apply at Pi.single i 1
  have h_eval :
      fderiv ℝ g x (Pi.single i 1) =
      fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) := by
    rw [h_fderiv_g]
    rfl
  -- And `fderiv g x (Pi.single i 1) = c · deriv²(hermiteEval (α i)) (x i)`
  -- via the slice + chain rule:
  have h_g_diff : DifferentiableAt ℝ g x := by
    rw [h_g]
    exact T.differentiableAt.comp x h_fderiv_diff
  have h_chain : HasDerivAt (fun s => g (Function.update x i s))
      (fderiv ℝ g x (Pi.single i 1)) (x i) := by
    have h_update := hasDerivAt_update x i (x i)
    have h_g_fderiv : HasFDerivAt g (fderiv ℝ g x) x := h_g_diff.hasFDerivAt
    have h_eq2 : x = Function.update x i (x i) := (Function.update_eq_self i x).symm
    exact HasFDerivAt.comp_hasDerivAt_of_eq (x := x i) (l := g)
      (l' := fderiv ℝ g x) (y := x)
      (f := Function.update x i) (f' := Pi.single i 1)
      h_g_fderiv h_update h_eq2
  have h_slice := fderiv_apply_single_slice_HasDerivAt α x i
  rw [← h_eval]
  exact h_chain.unique h_slice

/-- **Multivariate Hermite polynomials are OU eigenfunctions:**
`L H_α = -|α| · H_α`.

**Proof:** Slice each coordinate:
`hermiteMultiEval α (update x i s) = c_i(x) · hermiteEval (α i) s`
where `c_i(x) := ∏_{j ≠ i} hermiteEval (α j) (x j)`. The 1D and 2D
partial derivatives factor through `c_i(x)`, so the i-th term of
`ouGenerator n` is `c_i(x) · ouGenerator1D (hermiteEval (α i)) (x i)`.
By `ouGenerator1D_hermiteEval` this equals
`c_i(x) · (-α_i) · hermiteEval (α i) (x i) = -α_i · hermiteMultiEval α x`.
Summing over i gives `-(∑_i α_i) · hermiteMultiEval α x =
-(MultiIndex.totalDegree α) · hermiteMultiEval α x`. -/
theorem ouGenerator_hermiteMultiEval {n : ℕ} (α : Fin n → ℕ)
    (x : Fin n → ℝ) :
    ouGenerator n (hermiteMultiEval α) x =
      -(MultiIndex.totalDegree α : ℝ) * hermiteMultiEval α x := by
  classical
  unfold ouGenerator MultiIndex.totalDegree
  -- Rewrite each fderiv term using the slicing lemmas.
  have h_partial : ∀ i : Fin n,
      fderiv ℝ (hermiteMultiEval α) x (Pi.single i 1) =
        hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i) := by
    intro i; exact fderiv_hermiteMultiEval_apply_single α x i
  have h_partial2 : ∀ i : Fin n,
      fderiv ℝ (fderiv ℝ (hermiteMultiEval α)) x (Pi.single i 1) (Pi.single i 1) =
        hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) := by
    intro i; exact fderiv_fderiv_apply_single_single α x i
  simp_rw [h_partial, h_partial2]
  -- Now: ∑_i c_i · (deriv²(hermiteEval (α i)) (x i)) - ∑_i x i · (c_i · deriv(hermiteEval (α i)) (x i))
  --   = ∑_i c_i · ouGenerator1D(hermiteEval (α i))(x i)
  --   = ∑_i c_i · (-α_i) · hermiteEval (α i) (x i)
  --   = -∑_i α_i · hermiteMultiEval α x
  rw [← Finset.sum_sub_distrib]
  rw [show (fun i : Fin n =>
      hermiteMultiCoprod α i x * deriv (deriv (hermiteEval (α i))) (x i) -
      x i * (hermiteMultiCoprod α i x * deriv (hermiteEval (α i)) (x i))) =
      (fun i => hermiteMultiCoprod α i x *
        (deriv (deriv (hermiteEval (α i))) (x i) -
         x i * deriv (hermiteEval (α i)) (x i))) from by
    funext i; ring]
  -- The bracket is `ouGenerator1D (hermiteEval (α i)) (x i)`
  rw [show (fun i : Fin n =>
        hermiteMultiCoprod α i x *
        (deriv (deriv (hermiteEval (α i))) (x i) -
         x i * deriv (hermiteEval (α i)) (x i))) =
      (fun i => hermiteMultiCoprod α i x * ouGenerator1D (hermiteEval (α i)) (x i)) from by
    funext i; rfl]
  -- Apply 1D OU theorem
  simp_rw [ouGenerator1D_hermiteEval]
  -- ∑_i c_i · (-α_i · hermiteEval (α i) (x i)) = ∑_i (-α_i · ∏_j hermiteEval (α j) (x j))
  -- and the latter = -(∑_i α_i) · hermiteMultiEval α x.
  rw [show (fun i : Fin n =>
        hermiteMultiCoprod α i x * (-((α i : ℝ)) * hermiteEval (α i) (x i))) =
      (fun i => -((α i : ℝ)) * hermiteMultiEval α x) from by
    funext i
    unfold hermiteMultiEval hermiteMultiCoprod
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
        (fun j => hermiteEval (α j) (x j)) (Finset.mem_univ i)]
    ring]
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]
  push_cast
  ring

/-- **The Ornstein–Uhlenbeck semigroup action on $L^2(\gamma_n)$.**

The OU semigroup $T_t$ acts on $L^2(\gamma_n)$ as a continuous linear
map: it is the heat semigroup of the OU generator
$L = \Delta - x \cdot \nabla$, equivalently the Mehler convolution
$(T_t f)(x) = \int f(e^{-t} x + \sqrt{1 - e^{-2t}}\, y)\, d\gamma_n(y)$.

This is declared as an opaque axiom; its constraining properties are
the chaos-action and hypercontractivity axioms below. A concrete
construction (Mehler formula) lives in
`Diffusion/OrnsteinUhlenbeck.lean` (skeleton). -/
axiom ouSemigroupAct (n : ℕ) (t : ℝ) :
    MeasureTheory.Lp ℝ 2 (stdGaussianFin n) →L[ℝ]
      MeasureTheory.Lp ℝ 2 (stdGaussianFin n)

/-- **The OU semigroup acts on $\mathcal H_k$ by $e^{-kt}$.**

The OU semigroup $T_t$ on $L^2(\gamma_n)$ commutes with the spectral
decomposition into Wiener chaos: each chaos $\mathcal H_k$ is
$T_t$-invariant, and $T_t$ restricts to multiplication by $e^{-kt}$
on it.

This is the semigroup-level reformulation of the eigenfunction
identity above. The connection: $T_t = e^{tL}$, so on the eigenspace
of $L$ with eigenvalue $-k$, $T_t$ is multiplication by $e^{-kt}$.

**Reference:** Janson, *Gaussian Hilbert Spaces*, Theorem 4.4 +
the OU semigroup's L²-spectral-resolution. Bakry-Gentil-Ledoux §2.7. -/
axiom ouSemigroupAct_eq_smul_of_mem_wienerChaos {n : ℕ} (k : ℕ)
    (t : ℝ) (_ht : 0 ≤ t)
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n))
    (_hf : f ∈ wienerChaos n k) :
    ouSemigroupAct n t f = Real.exp (-(k : ℝ) * t) • f

/-- **Nelson's hypercontractive bound for the OU semigroup.**

For any $p \ge 2$ and $t \ge 0$ with $e^{2t} \ge p - 1$, the OU
semigroup $T_t$ maps $L^2(\gamma_n)$ to $L^p(\gamma_n)$ with operator
norm $\le 1$:
$$
\|T_t f\|_{L^p(\gamma_n)} \;\le\; \|f\|_{L^2(\gamma_n)}.
$$

This is the original "Nelson bound" (Nelson 1973), equivalent to the
Gaussian log-Sobolev inequality (Gross 1975) plus the Bakry-Émery
curvature lower bound for OU.

**Reference:** E. Nelson, *The free Markoff field*, J. Funct. Anal.
12 (1973), §3. Bakry-Gentil-Ledoux Thm 5.2.3. -/
axiom ouSemigroupAct_eLpNorm_hypercontractive {n : ℕ}
    (p : ℝ) (hp : 2 ≤ p)
    (t : ℝ) (_ht : 0 ≤ t)
    (_h_nelson : p - 1 ≤ Real.exp (2 * t))
    (f : MeasureTheory.Lp ℝ 2 (stdGaussianFin n)) :
    MeasureTheory.eLpNorm
        ((ouSemigroupAct n t f : (Fin n → ℝ) → ℝ))
        (ENNReal.ofReal p) (stdGaussianFin n) ≤
      MeasureTheory.eLpNorm
        ((f : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)

end GaussianField.Chaos
