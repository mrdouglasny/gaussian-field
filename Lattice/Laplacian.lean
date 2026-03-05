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
    (i : Fin d) (c : ZMod N) :
    (fun j => if j = i then x j + c else x j) = x + Pi.single i c := by
  ext j; simp only [Pi.add_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

private lemma update_sub_eq {d N : ℕ} [NeZero N] (x : FinLatticeSites d N)
    (i : Fin d) (c : ZMod N) :
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
    ∑ x, f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : ZMod N)) +
      g (x - Pi.single i (1 : ZMod N))) - 2 * g x)) =
    ∑ x, a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : ZMod N)) +
      f (x - Pi.single i (1 : ZMod N))) - 2 * f x) * g x := by
  -- Expand both sides into three terms
  have lhs_expand : ∀ x : FinLatticeSites d N,
      f x * (a⁻¹ ^ 2 * ((g (x + Pi.single i (1 : ZMod N)) +
        g (x - Pi.single i (1 : ZMod N))) - 2 * g x)) =
      a⁻¹ ^ 2 * (f x * g (x + Pi.single i 1)) +
      a⁻¹ ^ 2 * (f x * g (x - Pi.single i 1)) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  have rhs_expand : ∀ x : FinLatticeSites d N,
      a⁻¹ ^ 2 * ((f (x + Pi.single i (1 : ZMod N)) +
        f (x - Pi.single i (1 : ZMod N))) - 2 * f x) * g x =
      a⁻¹ ^ 2 * (f (x + Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (f (x - Pi.single i 1) * g x) +
      a⁻¹ ^ 2 * (-(2 : ℝ) * (f x * g x)) := by intro; ring
  simp_rw [lhs_expand, rhs_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Diagonal terms match. Reindex the shift terms.
  have h1 : ∑ x, f x * g (x + Pi.single i (1 : ZMod N)) =
      ∑ x, f (x - Pi.single i (1 : ZMod N)) * g x :=
    sum_mul_shift_fwd f g _
  have h2 : ∑ x, f x * g (x - Pi.single i (1 : ZMod N)) =
      ∑ x, f (x + Pi.single i (1 : ZMod N)) * g x :=
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
    Fintype.sum_equiv (Equiv.addRight (Pi.single i (1 : ZMod N)))
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
  let _ha := ha
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

/-- The ℓ¹ norm is invariant under negation. -/
private lemma latticeNorm_neg {d : ℕ} (v : Fin d → ℤ) :
    latticeNorm (-v) = latticeNorm v := by
  simp only [latticeNorm, Pi.neg_apply, Int.cast_neg, abs_neg]

/-- Shifting a rapidly decaying function by a bounded vector preserves rapid decay. -/
private lemma shift_rapid_decay {d : ℕ} (f : RapidDecayLattice d)
    (v : Fin d → ℤ) (hv : latticeNorm v ≤ 1) (k : ℕ) :
    Summable (fun x => |f.val (x + v)| * (1 + latticeNorm x) ^ k) := by
  -- Bound: (1+‖x‖) ≤ 2(1+‖x+v‖) because ‖x‖ ≤ ‖x+v‖ + ‖v‖ ≤ ‖x+v‖ + 1
  apply Summable.of_nonneg_of_le
    (fun x => mul_nonneg (abs_nonneg _) (RapidDecayLattice.weight_nonneg x k))
  · intro x
    have h_norm : latticeNorm x ≤ latticeNorm (x + v) + 1 := by
      have h1 : latticeNorm x = latticeNorm (fun i => (x + v) i + (-v) i) := by
        congr 1; ext j; simp
      have h2 := latticeNorm_triangle (x + v) (-v)
      have h3 : latticeNorm (-v) = latticeNorm v := latticeNorm_neg v
      linarith
    have h_le : 1 + latticeNorm x ≤ 2 * (1 + latticeNorm (x + v)) := by
      have := latticeNorm_nonneg (x + v)
      linarith
    calc |f.val (x + v)| * (1 + latticeNorm x) ^ k
        ≤ |f.val (x + v)| * (2 * (1 + latticeNorm (x + v))) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_left₀ (by linarith [latticeNorm_nonneg x]) h_le k
      _ = 2 ^ k * (|f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k) := by
          rw [mul_pow]; ring
  · -- The upper bound is summable: reindex y = x + v
    have h_sum : Summable (fun x => |f.val (x + v)| *
        (1 + latticeNorm (x + v)) ^ k) := by
      show Summable ((fun y => |f.val y| * (1 + latticeNorm y) ^ k) ∘ (· + v))
      exact (Equiv.summable_iff (Equiv.addRight v)).mpr (f.rapid_decay k)
    exact h_sum.const_smul (2 ^ k : ℝ)

/-- The raw function for the infinite Laplacian. -/
private def infiniteLaplacianFun (d : ℕ) (a : ℝ)
    (f : RapidDecayLattice d) (x : Fin d → ℤ) : ℝ :=
  a⁻¹ ^ 2 * ∑ i : Fin d,
    (f.val (fun j => x j + stdBasisInt d i j) +
     f.val (fun j => x j - stdBasisInt d i j) -
     2 * f.val x)

/-- Tsum bound for shifted rapid decay: the weighted tsum of a shift is bounded by
2^k times the original weighted tsum. -/
private lemma shift_rapid_decay_tsum_le {d : ℕ} (f : RapidDecayLattice d)
    (v : Fin d → ℤ) (hv : latticeNorm v ≤ 1) (k : ℕ) :
    ∑' x, |f.val (x + v)| * (1 + latticeNorm x) ^ k ≤
    2 ^ k * ∑' x, |f.val x| * (1 + latticeNorm x) ^ k := by
  have h_pw : ∀ x : Fin d → ℤ, |f.val (x + v)| * (1 + latticeNorm x) ^ k ≤
      2 ^ k * (|f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k) := by
    intro x
    have h_norm : latticeNorm x ≤ latticeNorm (x + v) + 1 := by
      have h1 : latticeNorm x = latticeNorm (fun i => (x + v) i + (-v) i) := by
        congr 1; ext j; simp
      have h2 := latticeNorm_triangle (x + v) (-v)
      have h3 : latticeNorm (-v) = latticeNorm v := latticeNorm_neg v
      linarith
    have h_le : 1 + latticeNorm x ≤ 2 * (1 + latticeNorm (x + v)) := by
      have := latticeNorm_nonneg (x + v)
      linarith
    calc |f.val (x + v)| * (1 + latticeNorm x) ^ k
        ≤ |f.val (x + v)| * (2 * (1 + latticeNorm (x + v))) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_left₀ (by linarith [latticeNorm_nonneg x]) h_le k
      _ = 2 ^ k * (|f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k) := by
          rw [mul_pow]; ring
  -- Reindex the upper bound sum: y = x + v
  have h_reindex : ∑' x, |f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k =
      ∑' y, |f.val y| * (1 + latticeNorm y) ^ k := by
    show ∑' x, ((fun y => |f.val y| * (1 + latticeNorm y) ^ k) (x + v)) =
      ∑' y, |f.val y| * (1 + latticeNorm y) ^ k
    exact Equiv.tsum_eq (Equiv.addRight v)
      (fun y => |f.val y| * (1 + latticeNorm y) ^ k)
  calc ∑' x, |f.val (x + v)| * (1 + latticeNorm x) ^ k
      ≤ ∑' x, 2 ^ k * (|f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k) :=
        (shift_rapid_decay f v hv k).tsum_le_tsum h_pw
          ((f.rapid_decay k).comp_injective (Equiv.addRight v).injective |>.const_smul (2 ^ k : ℝ))
    _ = 2 ^ k * ∑' x, |f.val (x + v)| * (1 + latticeNorm (x + v)) ^ k := tsum_mul_left
    _ = 2 ^ k * ∑' y, |f.val y| * (1 + latticeNorm y) ^ k := by rw [h_reindex]

/-- Summability of shifted terms for the negative basis direction. -/
private lemma shift_neg_rapid_decay {d : ℕ} (f : RapidDecayLattice d)
    (i : Fin d) (k : ℕ) :
    Summable (fun x => |f.val (fun j => x j - stdBasisInt d i j)| *
      (1 + latticeNorm x) ^ k) := by
  have hv : latticeNorm (fun j => -stdBasisInt d i j) ≤ 1 := by
    rw [show (fun j => -stdBasisInt d i j) = -(stdBasisInt d i) from by ext j; simp]
    rw [latticeNorm_neg]; exact le_of_eq (latticeNorm_stdBasis i)
  have h_eq : ∀ x : Fin d → ℤ,
      (fun j => x j - stdBasisInt d i j) = (x + fun j => -stdBasisInt d i j) := by
    intro x; ext j; simp [Pi.add_apply, sub_eq_add_neg]
  simp_rw [h_eq]
  exact shift_rapid_decay f _ hv k

/-- Tsum bound for negative shifted rapid decay. -/
private lemma shift_neg_rapid_decay_tsum_le {d : ℕ} (f : RapidDecayLattice d)
    (i : Fin d) (k : ℕ) :
    ∑' x, |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k ≤
    2 ^ k * ∑' x, |f.val x| * (1 + latticeNorm x) ^ k := by
  have hv : latticeNorm (fun j => -stdBasisInt d i j) ≤ 1 := by
    rw [show (fun j => -stdBasisInt d i j) = -(stdBasisInt d i) from by ext j; simp]
    rw [latticeNorm_neg]; exact le_of_eq (latticeNorm_stdBasis i)
  show ∑' x, |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k ≤
    2 ^ k * ∑' x, |f.val x| * (1 + latticeNorm x) ^ k
  have : (fun x : Fin d → ℤ => |f.val (fun j => x j - stdBasisInt d i j)| *
      (1 + latticeNorm x) ^ k) =
    (fun x => |f.val (x + fun j => -stdBasisInt d i j)| *
      (1 + latticeNorm x) ^ k) := by
    ext x; congr 1
  rw [this]
  exact shift_rapid_decay_tsum_le f _ hv k

/-- The infinite Laplacian preserves rapid decay. -/
private lemma infiniteLaplacian_rapid_decay (d : ℕ) (a : ℝ)
    (f : RapidDecayLattice d) (k : ℕ) :
    Summable (fun x => |infiniteLaplacianFun d a f x| * (1 + latticeNorm x) ^ k) := by
  -- Strategy: bound |Δf(x)| * w(x) ≤ sum of shifted terms, each summable.
  -- Build the summable upper bound as a sum over directions
  have h_shift_plus : ∀ i : Fin d, Summable (fun x =>
      |f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k) :=
    fun i => shift_rapid_decay f (stdBasisInt d i) (le_of_eq (latticeNorm_stdBasis i)) k
  have h_shift_minus : ∀ i : Fin d, Summable (fun x =>
      |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k) :=
    fun i => shift_neg_rapid_decay f i k
  have h_diag : Summable (fun x => |f.val x| * (1 + latticeNorm x) ^ k) :=
    f.rapid_decay k
  -- The summable upper bound per direction
  have h_dir_summable : ∀ i : Fin d, Summable (fun x =>
      |f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
      |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
      2 * (|f.val x| * (1 + latticeNorm x) ^ k)) := by
    intro i
    apply Summable.add
    · exact (h_shift_plus i).add (h_shift_minus i)
    · show Summable (fun x => (2 : ℝ) • (|f.val x| * (1 + latticeNorm x) ^ k))
      exact h_diag.const_smul 2
  -- Sum over all d directions is summable
  have h_all_summable : Summable (fun x => ∑ i : Fin d,
      (|f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
       |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
       2 * (|f.val x| * (1 + latticeNorm x) ^ k))) :=
    summable_sum (fun i _ => h_dir_summable i)
  -- Scale by |a⁻¹|²
  have h_ub_summable : Summable (fun x => |a⁻¹| ^ 2 * ∑ i : Fin d,
      (|f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
       |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
       2 * (|f.val x| * (1 + latticeNorm x) ^ k))) :=
    h_all_summable.const_smul (|a⁻¹| ^ 2)
  -- Pointwise bound for each x
  have h_pw : ∀ x, |infiniteLaplacianFun d a f x| * (1 + latticeNorm x) ^ k ≤
      |a⁻¹| ^ 2 * ∑ i : Fin d,
        (|f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
         |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
         2 * (|f.val x| * (1 + latticeNorm x) ^ k)) := by
    intro x
    simp only [infiniteLaplacianFun]
    rw [abs_mul, abs_pow]
    have hw := RapidDecayLattice.weight_nonneg x k
    -- Bound |∑ ...| ≤ ∑ (|f(x+eᵢ)| + |f(x-eᵢ)| + 2|f(x)|)
    have h_abs_sum : |∑ i : Fin d, (f.val (fun j => x j + stdBasisInt d i j) +
            f.val (fun j => x j - stdBasisInt d i j) - 2 * f.val x)| ≤
        ∑ i : Fin d,
          (|f.val (fun j => x j + stdBasisInt d i j)| +
           |f.val (fun j => x j - stdBasisInt d i j)| +
           2 * |f.val x|) := by
      calc |∑ i : Fin d, _|
          ≤ ∑ i : Fin d, |f.val (fun j => x j + stdBasisInt d i j) +
              f.val (fun j => x j - stdBasisInt d i j) - 2 * f.val x| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum; intro i _
          set a₁ := f.val (fun j => x j + stdBasisInt d i j)
          set a₂ := f.val (fun j => x j - stdBasisInt d i j)
          calc |a₁ + a₂ - 2 * f.val x|
              ≤ |a₁ + a₂| + |2 * f.val x| := by
                have := abs_add_le (a₁ + a₂) (-(2 * f.val x))
                rwa [abs_neg, ← sub_eq_add_neg] at this
            _ ≤ (|a₁| + |a₂|) + 2 * |f.val x| := by
                have := abs_add_le a₁ a₂
                rw [abs_mul, abs_of_nonneg (by norm_num : (2 : ℝ) ≥ 0)]
                linarith
    -- Combine: |a⁻¹|² * |∑...| * w ≤ |a⁻¹|² * ∑(abs terms) * w = |a⁻¹|² * ∑(abs*w terms)
    calc |a⁻¹| ^ 2 * |∑ i : Fin d, _| * (1 + latticeNorm x) ^ k
        ≤ |a⁻¹| ^ 2 * (∑ i : Fin d,
            (|f.val (fun j => x j + stdBasisInt d i j)| +
             |f.val (fun j => x j - stdBasisInt d i j)| +
             2 * |f.val x|)) * (1 + latticeNorm x) ^ k := by
          gcongr
      _ = |a⁻¹| ^ 2 * ∑ i : Fin d,
            (|f.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             |f.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             2 * (|f.val x| * (1 + latticeNorm x) ^ k)) := by
          rw [mul_assoc, Finset.sum_mul]
          congr 1; apply Finset.sum_congr rfl; intro i _; ring
  exact h_ub_summable.of_nonneg_of_le
    (fun x => mul_nonneg (abs_nonneg _) (RapidDecayLattice.weight_nonneg x k)) h_pw

/-- The infinite Laplacian as a linear map on rapid decay functions. -/
private def infiniteLaplacianLM (d : ℕ) (a : ℝ) :
    RapidDecayLattice d →ₗ[ℝ] RapidDecayLattice d where
  toFun f := ⟨infiniteLaplacianFun d a f, infiniteLaplacian_rapid_decay d a f⟩
  map_add' f g := by
    ext x; simp only [infiniteLaplacianFun, RapidDecayLattice.add_val]
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1; apply Finset.sum_congr rfl; intro i _; ring
  map_smul' r f := by
    ext x; simp only [infiniteLaplacianFun, RapidDecayLattice.smul_val, RingHom.id_apply]
    -- Factor r out of sum, commute with a⁻¹²
    have h_sum_eq : ∀ i : Fin d,
        r * f.val (fun j => x j + stdBasisInt d i j) +
        r * f.val (fun j => x j - stdBasisInt d i j) -
        2 * (r * f.val x) =
        r * (f.val (fun j => x j + stdBasisInt d i j) +
             f.val (fun j => x j - stdBasisInt d i j) -
             2 * f.val x) := fun i => by ring
    simp_rw [h_sum_eq, ← Finset.mul_sum, ← mul_assoc, mul_comm (a⁻¹ ^ 2) r]

/-- The discrete Laplacian on ℤ^d with spacing `a`.
Preserves rapid decay since it's a finite difference operator. -/
noncomputable def infiniteLaplacian (d : ℕ) (a : ℝ) :
    RapidDecayLattice d →L[ℝ] RapidDecayLattice d where
  toLinearMap := infiniteLaplacianLM d a
  cont := by
    apply Seminorm.continuous_from_bounded RapidDecayLattice.lattice_withSeminorms
      RapidDecayLattice.lattice_withSeminorms
    intro k
    -- For each output seminorm k, bound by input seminorm k with constant
    -- C = |a⁻¹|² * d * (2^(k+1) + 2). Each shifted tsum ≤ 2^k * seminorm_k(f).
    set C_val : ℝ := |a⁻¹| ^ 2 * (↑d * (2 * 2 ^ k + 2))
    have hC_nonneg : 0 ≤ C_val := by positivity
    refine ⟨{k}, ⟨⟨C_val, hC_nonneg⟩, fun g => ?_⟩⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, Seminorm.smul_apply, NNReal.smul_def,
      NNReal.coe_mk]
    -- Goal: seminorm_k(Δg) ≤ C * seminorm_k(g)
    show ∑' x, |(infiniteLaplacianLM d a g).val x| * (1 + latticeNorm x) ^ k ≤
      C_val * (∑' x, |g.val x| * (1 + latticeNorm x) ^ k)
    -- The LM value is just infiniteLaplacianFun
    change ∑' x, |infiniteLaplacianFun d a g x| * (1 + latticeNorm x) ^ k ≤
      C_val * (∑' x, |g.val x| * (1 + latticeNorm x) ^ k)
    set S := ∑' x, |g.val x| * (1 + latticeNorm x) ^ k
    -- Pointwise bound: |Δg(x)| * w ≤ |a⁻¹|² * ∑_i (|g(x+eᵢ)|*w + |g(x-eᵢ)|*w + 2*|g(x)|*w)
    -- (Same as in the rapid decay proof)
    have h_pw : ∀ x, |infiniteLaplacianFun d a g x| * (1 + latticeNorm x) ^ k ≤
        |a⁻¹| ^ 2 * ∑ i : Fin d,
          (|g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
           |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
           2 * (|g.val x| * (1 + latticeNorm x) ^ k)) := by
      intro x
      simp only [infiniteLaplacianFun]
      rw [abs_mul, abs_pow]
      have hw := RapidDecayLattice.weight_nonneg x k
      have h_abs_sum : |∑ i : Fin d, (g.val (fun j => x j + stdBasisInt d i j) +
              g.val (fun j => x j - stdBasisInt d i j) - 2 * g.val x)| ≤
          ∑ i : Fin d,
            (|g.val (fun j => x j + stdBasisInt d i j)| +
             |g.val (fun j => x j - stdBasisInt d i j)| +
             2 * |g.val x|) := by
        calc |∑ i : Fin d, _|
            ≤ ∑ i : Fin d, |g.val (fun j => x j + stdBasisInt d i j) +
                g.val (fun j => x j - stdBasisInt d i j) - 2 * g.val x| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum; intro i _
            set a₁ := g.val (fun j => x j + stdBasisInt d i j)
            set a₂ := g.val (fun j => x j - stdBasisInt d i j)
            calc |a₁ + a₂ - 2 * g.val x|
                ≤ |a₁ + a₂| + |2 * g.val x| := by
                  have := abs_add_le (a₁ + a₂) (-(2 * g.val x))
                  rwa [abs_neg, ← sub_eq_add_neg] at this
              _ ≤ (|a₁| + |a₂|) + 2 * |g.val x| := by
                  have := abs_add_le a₁ a₂
                  rw [abs_mul, abs_of_nonneg (by norm_num : (2 : ℝ) ≥ 0)]
                  linarith
      calc |a⁻¹| ^ 2 * |∑ i : Fin d, _| * (1 + latticeNorm x) ^ k
          ≤ |a⁻¹| ^ 2 * (∑ i : Fin d,
              (|g.val (fun j => x j + stdBasisInt d i j)| +
               |g.val (fun j => x j - stdBasisInt d i j)| +
               2 * |g.val x|)) * (1 + latticeNorm x) ^ k := by gcongr
        _ = |a⁻¹| ^ 2 * ∑ i : Fin d,
              (|g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
               |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
               2 * (|g.val x| * (1 + latticeNorm x) ^ k)) := by
            rw [mul_assoc, Finset.sum_mul]
            congr 1; apply Finset.sum_congr rfl; intro i _; ring
    -- Take the tsum of both sides
    have h_ub_summable : Summable (fun x => |a⁻¹| ^ 2 * ∑ i : Fin d,
        (|g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
         |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
         2 * (|g.val x| * (1 + latticeNorm x) ^ k))) := by
      apply Summable.const_smul (b := |a⁻¹| ^ 2)
      apply summable_sum; intro i _
      apply Summable.add
      · exact (shift_rapid_decay g (stdBasisInt d i)
            (le_of_eq (latticeNorm_stdBasis i)) k).add (shift_neg_rapid_decay g i k)
      · show Summable (fun x => (2 : ℝ) • (|g.val x| * (1 + latticeNorm x) ^ k))
        exact (g.rapid_decay k).const_smul 2
    -- Step 1: tsum bound using pointwise inequality
    calc ∑' x, |infiniteLaplacianFun d a g x| * (1 + latticeNorm x) ^ k
        ≤ ∑' x, |a⁻¹| ^ 2 * ∑ i : Fin d,
            (|g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             2 * (|g.val x| * (1 + latticeNorm x) ^ k)) :=
          (infiniteLaplacian_rapid_decay d a g k).tsum_le_tsum h_pw h_ub_summable
    -- Step 2: Pull constant out and swap sum/tsum
      _ = |a⁻¹| ^ 2 * ∑ i : Fin d,
            ∑' x, (|g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k +
             2 * (|g.val x| * (1 + latticeNorm x) ^ k)) := by
          rw [tsum_mul_left]
          congr 1
          exact Summable.tsum_finsetSum (fun i _ => by
            apply Summable.add
            · exact (shift_rapid_decay g (stdBasisInt d i)
                  (le_of_eq (latticeNorm_stdBasis i)) k).add (shift_neg_rapid_decay g i k)
            · show Summable (fun x => (2 : ℝ) • (|g.val x| * (1 + latticeNorm x) ^ k))
              exact (g.rapid_decay k).const_smul 2)
    -- Step 3: Bound each direction's tsum
      _ ≤ |a⁻¹| ^ 2 * ∑ i : Fin d, (2 ^ k * S + 2 ^ k * S + 2 * S) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (abs_nonneg _) 2)
          apply Finset.sum_le_sum; intro i _
          -- Split tsum(A + B + C) ≤ tsum A + tsum B + tsum C then bound each
          set T_plus := fun x : Fin d → ℤ =>
            |g.val (fun j => x j + stdBasisInt d i j)| * (1 + latticeNorm x) ^ k
          set T_minus := fun x : Fin d → ℤ =>
            |g.val (fun j => x j - stdBasisInt d i j)| * (1 + latticeNorm x) ^ k
          set T_diag := fun x : Fin d → ℤ =>
            2 * (|g.val x| * (1 + latticeNorm x) ^ k)
          have hS_plus : Summable T_plus := by
            show Summable (fun x => |g.val (fun j => x j + stdBasisInt d i j)| *
              (1 + latticeNorm x) ^ k)
            exact shift_rapid_decay g (stdBasisInt d i) (le_of_eq (latticeNorm_stdBasis i)) k
          have hS_minus : Summable T_minus := shift_neg_rapid_decay g i k
          have hS_diag : Summable T_diag := by
            show Summable (fun x => (2 : ℝ) • (|g.val x| * (1 + latticeNorm x) ^ k))
            exact (g.rapid_decay k).const_smul 2
          have h_split : ∑' x, (T_plus x + T_minus x + T_diag x) =
              ∑' x, T_plus x + ∑' x, T_minus x + ∑' x, T_diag x := by
            rw [show (fun x => T_plus x + T_minus x + T_diag x) =
                 (fun x => (T_plus x + T_minus x) + T_diag x) from by ext; ring]
            rw [(hS_plus.add hS_minus).tsum_add hS_diag,
                hS_plus.tsum_add hS_minus]
          rw [h_split]
          have h1 : ∑' x, T_plus x ≤ 2 ^ k * S :=
            shift_rapid_decay_tsum_le g (stdBasisInt d i)
              (le_of_eq (latticeNorm_stdBasis i)) k
          have h2 : ∑' x, T_minus x ≤ 2 ^ k * S :=
            shift_neg_rapid_decay_tsum_le g i k
          have h3 : ∑' x, T_diag x = 2 * S := tsum_mul_left
          linarith
    -- Step 4: Simplify constant sum
      _ = C_val * S := by
          simp only [C_val, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
          ring

/-- The infinite Laplacian acts as the expected finite difference formula. -/
theorem infiniteLaplacian_apply (d : ℕ) (a : ℝ) (f : RapidDecayLattice d)
    (x : Fin d → ℤ) :
    (infiniteLaplacian d a f).val x =
    a⁻¹ ^ 2 * ∑ i : Fin d,
      (f.val (fun j => x j + stdBasisInt d i j) +
       f.val (fun j => x j - stdBasisInt d i j) -
       2 * f.val x) := rfl

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

/-- Eigenvalue of `-Δ_a` alone (no mass) on the finite torus.
Mode index `m : ℕ` decodes to multi-index `k ∈ (ZMod N)^d` via Fintype
enumeration. The eigenvalue is:
  `(4/a²) Σᵢ sin²(πkᵢ/N)`

These are nonneg (the zero mode has eigenvalue 0). Mass is NOT included —
it enters only through the mass operator and Green's function. This follows
the mass-separation convention from `HeatKernel/Bilinear.lean`, ensuring
correct tensor product factorization: `μ_{E₁⊗E₂} = μ_{E₁} + μ_{E₂}`. -/
def latticeLaplacianEigenvalue (d N : ℕ) [NeZero N] (a : ℝ) (m : ℕ) : ℝ :=
  if h : m < Fintype.card (FinLatticeSites d N) then
    let k := (Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩
    (4 / a ^ 2) * ∑ i : Fin d, sin (π * (ZMod.val (k i) : ℝ) / N) ^ 2
  else
    0  -- default for out-of-range indices

/-- Laplacian eigenvalues are nonneg. -/
theorem latticeLaplacianEigenvalue_nonneg (d N : ℕ) [NeZero N] (a : ℝ) (m : ℕ) :
    0 ≤ latticeLaplacianEigenvalue d N a m := by
  unfold latticeLaplacianEigenvalue
  split_ifs with h
  · apply mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact le_refl _

/-- Eigenvalue of `-Δ_a + m²` on the finite torus.
Defined as `latticeLaplacianEigenvalue + mass²`. -/
def latticeEigenvalue (d N : ℕ) [NeZero N] (a mass : ℝ) (m : ℕ) : ℝ :=
  latticeLaplacianEigenvalue d N a m + mass ^ 2

/-- `latticeEigenvalue` unfolds to the explicit formula with mass. -/
theorem latticeEigenvalue_eq (d N : ℕ) [NeZero N] (a mass : ℝ) (m : ℕ) :
    latticeEigenvalue d N a mass m = latticeLaplacianEigenvalue d N a m + mass ^ 2 :=
  rfl

/-- Eigenvalues are strictly positive when mass > 0. -/
theorem latticeEigenvalue_pos (d N : ℕ) [NeZero N] (a mass : ℝ)
    (_ha : 0 < a) (hmass : 0 < mass) (m : ℕ) :
    0 < latticeEigenvalue d N a mass m := by
  rw [latticeEigenvalue_eq]
  linarith [latticeLaplacianEigenvalue_nonneg d N a m, sq_pos_of_pos hmass]

end GaussianField
