/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Discrete Laplacian with Lattice Spacing

Defines the discrete Laplacian on both finite (periodic) and infinite lattices,
parametrized by lattice spacing `a : ℝ`. Also defines the massive operator
`-Δ_a + m²` and its eigenvalues on the finite lattice.

## Main definitions

- `finiteLaplacian d N a` — discrete Laplacian on the finite torus
- `infiniteLaplacian d a` — discrete Laplacian on ℤ^d
- `massOperator d N a mass` — the massive operator `-Δ_a + m²`
- `latticeEigenvalue d N a mass m` — eigenvalues of the mass operator

## Mathematical background

The discrete Laplacian with spacing `a` is:
  `(Δ_a f)(x) = (1/a²) Σ_{i=1}^d [f(x + eᵢ) + f(x - eᵢ) - 2f(x)]`

On the finite torus with periodic BC, it has eigenvalues:
  `λ_k = -(4/a²) Σᵢ sin²(πkᵢ/N)`

The mass operator `-Δ_a + m²` is positive definite when `m > 0`.
-/

import Lattice.Sites
import Lattice.FiniteField
import Lattice.RapidDecayLattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

namespace GaussianField

open Real

/-! ## Finite Laplacian -/

/-- The discrete Laplacian on the finite torus (ℤ/Nℤ)^d with spacing `a`.

`(Δ_a f)(x) = (1/a²) Σᵢ [f(x + eᵢ) + f(x - eᵢ) - 2f(x)]`

where addition is modulo N (periodic boundary conditions). -/
def finiteLaplacianFun (d N : ℕ) [NeZero N] (a : ℝ) (f : FinLatticeField d N)
    (x : FinLatticeSites d N) : ℝ :=
  a⁻¹ ^ 2 * ∑ i : Fin d,
    (f (fun j => if j = i then x j + 1 else x j) +
     f (fun j => if j = i then x j - 1 else x j) -
     2 * f x)

/-- The finite Laplacian as a continuous linear map. Continuity is automatic
since FinLatticeField d N is finite-dimensional. -/
def finiteLaplacianLM (d N : ℕ) [NeZero N] (a : ℝ) :
    FinLatticeField d N →ₗ[ℝ] FinLatticeField d N where
  toFun := finiteLaplacianFun d N a
  map_add' := fun f g => by
    funext x; simp only [finiteLaplacianFun, Pi.add_apply]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  map_smul' := fun r f => by
    funext x; simp only [finiteLaplacianFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    -- Factor r out of each summand, then pull through sum and a⁻¹²
    have : ∀ i : Fin d,
        (r * (f fun j => if j = i then x j + 1 else x j)) +
        (r * (f fun j => if j = i then x j - 1 else x j)) -
        2 * (r * f x) =
        r * (((f fun j => if j = i then x j + 1 else x j) +
              (f fun j => if j = i then x j - 1 else x j)) -
             2 * f x) := fun i => by ring
    simp_rw [this, ← Finset.mul_sum, ← mul_assoc, mul_comm (a⁻¹ ^ 2) r]

/-- The finite Laplacian as a continuous linear map. Continuity is automatic
since FinLatticeField d N is finite-dimensional. -/
noncomputable def finiteLaplacian (d N : ℕ) [NeZero N] (a : ℝ) :
    FinLatticeField d N →L[ℝ] FinLatticeField d N :=
  { finiteLaplacianLM d N a with
    cont := (finiteLaplacianLM d N a).continuous_of_finiteDimensional }

/-! ## Properties of the finite Laplacian -/

/-- The finite Laplacian is self-adjoint (symmetric matrix).
Proof: exchange of summation indices using periodicity. -/
private lemma update_add_eq {d N : ℕ} [NeZero N] (x : FinLatticeSites d N)
    (i : Fin d) (c : Fin N) :
    (fun j => if j = i then x j + c else x j) = x + Pi.single i c := by
  ext j; simp only [Pi.add_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

private lemma update_sub_eq {d N : ℕ} [NeZero N] (x : FinLatticeSites d N)
    (i : Fin d) (c : Fin N) :
    (fun j => if j = i then x j - c else x j) = x - Pi.single i c := by
  ext j; simp only [Pi.sub_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

private lemma sum_mul_shift_fwd {d N : ℕ} [NeZero N]
    (h k : FinLatticeField d N) (v : FinLatticeSites d N) :
    ∑ x, h x * k (x + v) = ∑ x, h (x - v) * k x := by
  symm; exact Fintype.sum_equiv (Equiv.addRight (-v))
    (fun x => h (x - v) * k x) (fun x => h x * k (x + v))
    (fun x => by simp [sub_eq_add_neg])

private lemma sum_mul_shift_bwd {d N : ℕ} [NeZero N]
    (h k : FinLatticeField d N) (v : FinLatticeSites d N) :
    ∑ x, h x * k (x - v) = ∑ x, h (x + v) * k x := by
  symm; exact Fintype.sum_equiv (Equiv.addRight v)
    (fun x => h (x + v) * k x) (fun x => h x * k (x - v))
    (fun x => by simp [add_sub_cancel_right])

/-- Helper: The Laplacian inner product for a single direction, after expanding. -/
private lemma laplacian_direction_eq {d N : ℕ} [NeZero N]
    (f g : FinLatticeField d N) (i : Fin d) (a : ℝ) :
    ∑ x, f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : Fin N)) +
      g (x - Pi.single i (1 : Fin N))) - 2 * g x)) =
    ∑ x, a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : Fin N)) +
      f (x - Pi.single i (1 : Fin N))) - 2 * f x) * g x := by
  -- Expand both sides into three terms
  have lhs_expand : ∀ x : FinLatticeSites d N,
      f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : Fin N)) +
        g (x - Pi.single i (1 : Fin N))) - 2 * g x)) =
      a⁻¹ ^ 2 * (f x * g (x + Pi.single i 1)) +
      a⁻¹ ^ 2 * (f x * g (x - Pi.single i 1)) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  have rhs_expand : ∀ x : FinLatticeSites d N,
      a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : Fin N)) +
        f (x - Pi.single i (1 : Fin N))) - 2 * f x) * g x =
      a⁻¹ ^ 2 * (f (x + Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (f (x - Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  simp_rw [lhs_expand, rhs_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Diagonal terms match. Reindex the shift terms.
  have h1 : ∑ x, f x * g (x + Pi.single i (1 : Fin N)) =
      ∑ x, f (x - Pi.single i (1 : Fin N)) * g x :=
    sum_mul_shift_fwd f g _
  have h2 : ∑ x, f x * g (x - Pi.single i (1 : Fin N)) =
      ∑ x, f (x + Pi.single i (1 : Fin N)) * g x :=
    sum_mul_shift_bwd f g _
  rw [h1, h2]; ring

/-- The finite Laplacian is self-adjoint: ⟨f, Δg⟩ = ⟨Δf, g⟩. -/
theorem finiteLaplacian_selfAdjoint (d N : ℕ) [NeZero N] (a : ℝ)
    (f g : FinLatticeField d N) :
    ∑ x, f x * (finiteLaplacian d N a g) x =
    ∑ x, (finiteLaplacian d N a f) x * g x := by
  -- Unfold to the raw function definition
  change ∑ x, f x * finiteLaplacianFun d N a g x =
    ∑ x, finiteLaplacianFun d N a f x * g x
  simp only [finiteLaplacianFun]
  simp_rw [update_add_eq, update_sub_eq]
  -- Pull the direction sum outside and swap with the site sum
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  congr 1; ext i
  exact laplacian_direction_eq f g i a

/-- For each lattice direction, the inner product ∑ₓ f(x)·Δᵢf(x) equals
minus a sum of squares: -(∑ₓ (f(x+eᵢ) - f(x))²). -/
private lemma direction_sum_eq_neg_sq {d N : ℕ} [NeZero N]
    (f : FinLatticeField d N) (i : Fin d) :
    ∑ x : FinLatticeSites d N,
      f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
    -(∑ x : FinLatticeSites d N, (f (x + Pi.single i 1) - f x) ^ 2) := by
  have reindex_sq : ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) ^ 2 =
      ∑ x : FinLatticeSites d N, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : Fin N)))
      (fun x => f (x + Pi.single i 1) ^ 2) (fun x => f x ^ 2)
      (fun x => by simp)
  have shift_bwd : ∑ x : FinLatticeSites d N, f x * f (x - Pi.single i 1) =
      ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) * f x :=
    sum_mul_shift_bwd f f _
  have comm_sum : ∑ x : FinLatticeSites d N, f (x + Pi.single i 1) * f x =
      ∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have lhs_eq : ∑ x : FinLatticeSites d N,
      f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
      (∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1)) +
      (∑ x : FinLatticeSites d N, f x * f (x - Pi.single i 1)) +
      (-2) * (∑ x : FinLatticeSites d N, f x ^ 2) := by
    have h1 : ∀ x : FinLatticeSites d N,
        f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x) =
        f x * f (x + Pi.single i 1) + f x * f (x - Pi.single i 1) +
        (-2) * (f x ^ 2) := by intro; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [lhs_eq, shift_bwd, comm_sum]
  have rhs_eq : -(∑ x : FinLatticeSites d N, (f (x + Pi.single i 1) - f x) ^ 2) =
      -(∑ x : FinLatticeSites d N, f (x + Pi.single i 1) ^ 2) +
      2 * (∑ x : FinLatticeSites d N, f x * f (x + Pi.single i 1)) +
      (-1) * (∑ x : FinLatticeSites d N, f x ^ 2) := by
    have h2 : ∀ x : FinLatticeSites d N,
        (f (x + Pi.single i 1) - f x) ^ 2 =
        f (x + Pi.single i 1) ^ 2 + (-2) * (f x * f (x + Pi.single i 1)) +
        f x ^ 2 := by intro; ring
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [rhs_eq, reindex_sq]
  ring

/-- The finite Laplacian is negative semidefinite: ⟨f, Δf⟩ ≤ 0.
Proof: summation by parts gives -a⁻² Σᵢ Σₓ (f(x+eᵢ) - f(x))² ≤ 0. -/
theorem finiteLaplacian_neg_semidefinite (d N : ℕ) [NeZero N] (a : ℝ) (ha : 0 < a)
    (f : FinLatticeField d N) :
    ∑ x, f x * (finiteLaplacian d N a f) x ≤ 0 := by
  change ∑ x, f x * finiteLaplacianFun d N a f x ≤ 0
  simp only [finiteLaplacianFun]
  simp_rw [update_add_eq, update_sub_eq]
  -- Rewrite to a⁻¹² * ∑_i ∑_x f(x)·(D_i f)(x) and swap sums
  have step1 : (∑ x : FinLatticeSites d N,
      f x * (a⁻¹ ^ 2 * ∑ i : Fin d,
        (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x))) =
    a⁻¹ ^ 2 * ∑ i : Fin d, ∑ x : FinLatticeSites d N,
      (f x * (f (x + Pi.single i 1) + f (x - Pi.single i 1) - 2 * f x)) := by
    conv_lhs =>
      arg 2; ext x
      rw [mul_comm (f x) (a⁻¹ ^ 2 * _), mul_assoc, Finset.sum_mul]
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1; apply Finset.sum_congr rfl
    intro i _; apply Finset.sum_congr rfl
    intro x _; ring
  rw [step1]
  simp_rw [direction_sum_eq_neg_sq]
  apply mul_nonpos_of_nonneg_of_nonpos
  · exact sq_nonneg _
  · exact Finset.sum_nonpos (fun i _ =>
      neg_nonpos_of_nonneg (Finset.sum_nonneg (fun x _ => sq_nonneg _)))

/-! ## Infinite Laplacian -/

/-- The discrete Laplacian on ℤ^d with spacing `a`.
Preserves rapid decay since it's a finite difference operator. -/
axiom infiniteLaplacian (d : ℕ) (a : ℝ) :
    RapidDecayLattice d →L[ℝ] RapidDecayLattice d

/-- The infinite Laplacian acts as the expected finite difference formula. -/
axiom infiniteLaplacian_apply (d : ℕ) (a : ℝ) (f : RapidDecayLattice d)
    (x : Fin d → ℤ) :
    (infiniteLaplacian d a f).val x =
    a⁻¹ ^ 2 * ∑ i : Fin d,
      (f.val (fun j => x j + stdBasisInt d i j) +
       f.val (fun j => x j - stdBasisInt d i j) -
       2 * f.val x)

/-! ## Mass operator -/

/-- The mass operator `-Δ_a + m²` on the finite lattice.
This is the covariance operator's inverse in the lattice Gaussian measure. -/
def massOperator (d N : ℕ) [NeZero N] (a mass : ℝ) :
    FinLatticeField d N →L[ℝ] FinLatticeField d N :=
  -finiteLaplacian d N a + mass ^ 2 • ContinuousLinearMap.id ℝ _

/-- The mass operator is positive definite when mass > 0.
Proof: ⟨f, (-Δ+m²)f⟩ = -⟨f,Δf⟩ + m²‖f‖² ≥ m²‖f‖² > 0 for f ≠ 0. -/
theorem massOperator_pos_def (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) (hf : f ≠ 0) :
    0 < ∑ x, f x * (massOperator d N a mass f) x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have split : ∀ x : FinLatticeSites d N,
      f x * (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) =
      -(f x * (finiteLaplacian d N a f) x) + mass ^ 2 * f x ^ 2 := by
    intro x; ring
  simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have h_neg : 0 ≤ -(∑ x : FinLatticeSites d N, f x * (finiteLaplacian d N a f) x) :=
    neg_nonneg.mpr (finiteLaplacian_neg_semidefinite d N a ha f)
  have h_sq_pos : 0 < ∑ x : FinLatticeSites d N, f x ^ 2 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h; push_neg at h; exact hf (funext h)
    exact Finset.sum_pos' (fun x _ => sq_nonneg (f x)) ⟨x, Finset.mem_univ _, by positivity⟩
  linarith [mul_pos (sq_pos_of_pos hmass) h_sq_pos]

/-! ## Eigenvalues -/

/-- Eigenvalue of `-Δ_a + m²` on the finite torus.
Mode index `m : ℕ` decodes to multi-index `k ∈ (Fin N)^d` via Fintype
enumeration. The eigenvalue is:
  `(4/a²) Σᵢ sin²(πkᵢ/N) + mass²` -/
def latticeEigenvalue (d N : ℕ) [NeZero N] (a mass : ℝ) (m : ℕ) : ℝ :=
  if h : m < Fintype.card (FinLatticeSites d N) then
    let k := (Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩
    (4 / a ^ 2) * ∑ i : Fin d, sin (π * (k i : ℝ) / N) ^ 2 + mass ^ 2
  else
    mass ^ 2  -- default for out-of-range indices

/-- Eigenvalues are strictly positive when mass > 0. -/
theorem latticeEigenvalue_pos (d N : ℕ) [NeZero N] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (m : ℕ) :
    0 < latticeEigenvalue d N a mass m := by
  unfold latticeEigenvalue
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ (4 / a ^ 2) *
        ∑ i : Fin d, sin (π * ↑((Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩ i) / ↑N) ^ 2 := by
      apply mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith [sq_pos_of_pos hmass]
  · exact sq_pos_of_pos hmass

end GaussianField
