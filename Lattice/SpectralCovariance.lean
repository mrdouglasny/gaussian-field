/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Covariance Construction

Constructs the lattice covariance CLM `T : FinLatticeField → ℓ²` via the
spectral theorem for the mass operator matrix Q = -Δ + m².

The key property is `⟨Tf, Tg⟩_ℓ² = ⟨f, Q⁻¹g⟩_L²`, which is needed for the
density bridge (showing the Gaussian measure has density exp(-½⟨φ,Qφ⟩)).

## Main definitions

- `massOperatorMatrix` — the mass operator as a real symmetric matrix
- `spectralLatticeCovariance` — the CLM `T = Q^{-1/2}` into ℓ²

## Main theorems

- `massOperatorMatrix_isHermitian` — Q is symmetric
- `massOperatorMatrix_eigenvalues_pos` — eigenvalues of Q are positive
- `spectralLatticeCovariance_inner` — `⟨Tf, Tg⟩ = Σ_x f(x)(Q⁻¹g)(x)`
- `spectralLatticeCovariance_norm_sq_eq` — `‖Tf‖² = Σ_x f(x)(Q⁻¹f)(x)`

## References

- Reed-Simon, Vol. 1, §VI (Spectral theorem)
- Glimm-Jaffe, §19 (Gaussian measures and covariance operators)
-/

import Lattice.Laplacian
import Lattice.FiniteField
import HeatKernel.Axioms
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GaussianField

open MeasureTheory Matrix

variable (d N : ℕ) [NeZero N]

/-! ## Mass operator as a matrix -/

/-- The "matrix entries" of the mass operator: the bilinear form evaluated
on delta functions. `Q(x,y) = ⟨δ_x, (-Δ+m²)(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorEntry (a mass : ℝ)
    (x y : FinLatticeSites d N) : ℝ :=
  (massOperator d N a mass (finLatticeDelta d N y)) x

/-- The mass operator `Q = -Δ + m²` as a matrix indexed by lattice sites.
Entry `(x, y)` is `⟨δ_x, Q(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorMatrix (a mass : ℝ) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  fun x y => massOperatorEntry d N a mass x y

/-! ## Self-adjointness -/

/-- The mass operator is self-adjoint: `⟨f, Qg⟩ = ⟨Qf, g⟩`. -/
theorem massOperator_selfAdjoint (a mass : ℝ)
    (f g : FinLatticeField d N) :
    ∑ x, f x * (massOperator d N a mass g) x =
    ∑ x, (massOperator d N a mass f) x * g x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  -- Split into Laplacian and mass terms
  have split_l : ∀ x, f x * (-(finiteLaplacian d N a g) x + mass ^ 2 * g x) =
      -(f x * (finiteLaplacian d N a g) x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  have split_r : ∀ x, (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) * g x =
      -((finiteLaplacian d N a f) x * g x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  simp_rw [split_l, split_r, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  congr 1
  -- The Laplacian part follows from finiteLaplacian_selfAdjoint
  rw [finiteLaplacian_selfAdjoint d N a f g]

/-- The mass operator matrix is Hermitian (symmetric over ℝ).

Proof: Self-adjointness of Q applied to delta functions gives
`Q(x,y) = (Qδ_y)(x) = ⟨δ_x, Qδ_y⟩ = ⟨Qδ_x, δ_y⟩ = (Qδ_x)(y) = Q(y,x)`. -/
theorem massOperatorMatrix_isHermitian (a mass : ℝ) :
    (massOperatorMatrix d N a mass).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have h := massOperator_selfAdjoint d N a mass
    (finLatticeDelta d N j) (finLatticeDelta d N i)
  simpa [Matrix.conjTranspose, massOperatorMatrix, massOperatorEntry, finLatticeDelta] using h

/-! ## Eigenvectors and eigenvalues -/

/-- Abbreviation for the Hermiticity proof. -/
abbrev massMatrixHerm (a mass : ℝ) :=
  massOperatorMatrix_isHermitian d N a mass

/-- Eigenvalues of the mass operator matrix. -/
def massEigenvalues (a mass : ℝ) : FinLatticeSites d N → ℝ :=
  (massMatrixHerm d N a mass).eigenvalues

/-- Eigenvector orthonormal basis of the mass operator matrix. -/
def massEigenvectorBasis (a mass : ℝ) :
    OrthonormalBasis (FinLatticeSites d N) ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) :=
  (massMatrixHerm d N a mass).eigenvectorBasis

section
set_option linter.unusedSectionVars false
/-- Basis decomposition: any lattice field is a linear combination of deltas. -/
private lemma field_basis_decomp (φ : FinLatticeField d N) :
    φ = ∑ y : FinLatticeSites d N, φ y • finLatticeDelta d N y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
end

/-- The mass operator applied to f equals the matrix-vector product.

This bridges the CLM `massOperator` with the matrix `massOperatorMatrix`:
`(Q f)(x) = Σ_y Q(x,y) · f(y) = (M *ᵥ f)(x)`. -/
theorem massOperator_eq_matrix_mulVec (a mass : ℝ)
    (f : FinLatticeField d N) (x : FinLatticeSites d N) :
    (massOperator d N a mass f) x =
    (massOperatorMatrix d N a mass).mulVec f x := by
  -- (Q f)(x) = Σ_y Q(x,y) f(y) = (M *ᵥ f)(x) by linearity + basis expansion
  simp only [Matrix.mulVec, massOperatorMatrix]
  conv_lhs => rw [field_basis_decomp d N f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1; ext y
  -- f y * (Q δ_y)(x) = massOperatorEntry x y * f y
  unfold massOperatorEntry
  ring

/-- In eigenbasis coefficients, the mass operator acts by scalar multiplication
by the corresponding eigenvalue. -/
theorem massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff (a mass : ℝ)
    (f : FinLatticeField d N) (k : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (massOperator d N a mass f) x) =
      massEigenvalues d N a mass k *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
  have hswap := massOperator_selfAdjoint d N a mass
    (massEigenvectorBasis d N a mass k) f
  have hright :
      ∑ x : FinLatticeSites d N,
          (massOperator d N a mass (massEigenvectorBasis d N a mass k)) x * f x =
        massEigenvalues d N a mass k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
    have hmul :
        massOperator d N a mass (massEigenvectorBasis d N a mass k) =
          massEigenvalues d N a mass k • (massEigenvectorBasis d N a mass k) := by
      ext x
      rw [massOperator_eq_matrix_mulVec (d := d) (N := N) a mass
        (massEigenvectorBasis d N a mass k) x]
      simpa [massEigenvalues, massEigenvectorBasis] using
        congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
          (hA := massOperatorMatrix_isHermitian d N a mass) k) x
    rw [hmul]
    calc
      ∑ x : FinLatticeSites d N,
          (massEigenvalues d N a mass k *
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) * f x
          = ∑ x : FinLatticeSites d N,
              massEigenvalues d N a mass k *
                ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
            rw [Finset.mul_sum]
  rw [hright] at hswap
  exact hswap

/-- Parseval identity in the mass-operator eigenbasis, written in site
coordinates. -/
theorem massEigenbasis_sum_mul_sum_eq_site_inner (a mass : ℝ)
    (f g : FinLatticeField d N) :
    (∑ k : FinLatticeSites d N,
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x)) =
      ∑ x : FinLatticeSites d N, f x * g x := by
  let uf : EuclideanSpace ℝ (FinLatticeSites d N) :=
    (EuclideanSpace.equiv (FinLatticeSites d N) ℝ).symm f
  let ug : EuclideanSpace ℝ (FinLatticeSites d N) :=
    (EuclideanSpace.equiv (FinLatticeSites d N) ℝ).symm g
  have hparseval :=
    OrthonormalBasis.sum_inner_mul_inner (massEigenvectorBasis d N a mass) uf ug
  have hcoeff_left : ∀ k : FinLatticeSites d N,
      inner ℝ uf (massEigenvectorBasis d N a mass k) =
        ∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x := by
    intro k
    simp [uf, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have hcoeff_right : ∀ k : FinLatticeSites d N,
      inner ℝ (massEigenvectorBasis d N a mass k) ug =
        ∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x := by
    intro k
    simp [ug, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hinner :
      inner ℝ uf ug = ∑ x : FinLatticeSites d N, f x * g x := by
    simp [uf, ug, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  calc
    (∑ k : FinLatticeSites d N,
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x))
        = ∑ k : FinLatticeSites d N,
            inner ℝ uf (massEigenvectorBasis d N a mass k) *
              inner ℝ (massEigenvectorBasis d N a mass k) ug := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [hcoeff_left, hcoeff_right]
    _ = inner ℝ uf ug := hparseval
    _ = ∑ x : FinLatticeSites d N, f x * g x := hinner

/-- Spectral decomposition of the quadratic form of `massOperator`:
`∑ x, f x * (Q f) x = ∑ k, λ_k * c_k(f)^2`. -/
theorem massOperator_quadratic_eq_spectral (a mass : ℝ)
    (f : FinLatticeField d N) :
    (∑ x : FinLatticeSites d N, f x * (massOperator d N a mass f) x) =
      ∑ k : FinLatticeSites d N,
        massEigenvalues d N a mass k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
  have hparseval :=
    massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass f (massOperator d N a mass f)
  have hcoeff :
      ∀ k : FinLatticeSites d N,
        (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              (massOperator d N a mass f) x) =
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) := by
    intro k
    exact massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff
      (d := d) (N := N) a mass f k
  calc
    (∑ x : FinLatticeSites d N, f x * (massOperator d N a mass f) x)
        = ∑ k : FinLatticeSites d N,
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                (massOperator d N a mass f) x) := by
            symm
            exact hparseval
    _ = ∑ k : FinLatticeSites d N,
          (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
            (massEigenvalues d N a mass k *
              (∑ x : FinLatticeSites d N,
                (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [hcoeff k]
    _ = ∑ k : FinLatticeSites d N,
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          ring

/-- Eigenvalues of the mass operator are strictly positive.

Proof: Q is positive definite. For eigenvector e_k with eigenvalue λ_k:
`0 < ⟨e_k, Q e_k⟩ = λ_k ⟨e_k, e_k⟩ = λ_k`. -/
theorem massOperatorMatrix_eigenvalues_pos (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    0 < massEigenvalues d N a mass k := by
  let M : Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ := massOperatorMatrix d N a mass
  have hPosDef : M.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ?_
    refine ⟨massOperatorMatrix_isHermitian d N a mass, ?_⟩
    intro x hx
    have hpos := massOperator_pos_def d N a mass ha hmass x hx
    have hmul : M *ᵥ x = massOperator d N a mass x := by
      ext i
      symm
      exact massOperator_eq_matrix_mulVec d N a mass x i
    simpa [M, dotProduct, hmul] using hpos
  have hEigPos : ∀ i : FinLatticeSites d N, 0 < (massMatrixHerm d N a mass).eigenvalues i :=
    (Matrix.IsHermitian.posDef_iff_eigenvalues_pos
      (hA := massMatrixHerm d N a mass)).mp hPosDef
  simpa [massEigenvalues] using hEigPos k

/-! ## Spectral covariance CLM -/

/-- The spectral lattice covariance: `T = Q^{-1/2}` as a CLM into ℓ².

For `f : FinLatticeField d N`, defines:
  `(Tf)(m) = λ_m^{-1/2} · ⟪e_m, f⟫_L²`   for `m < N^d`
  `(Tf)(m) = 0`                              otherwise

where `{e_m}` is the eigenvector ONB of Q and `λ_m` its eigenvalues.
Maps into `ell2'` via the Fintype enumeration of lattice sites. -/
noncomputable def spectralLatticeCovariance (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' := by
  -- Build as a CLM via finite-dimensionality (any linear map is continuous)
  -- The linear map sends f to ∑_k λ_k^{-1/2} ⟪e_k, f⟫ · ℓ²_k
  set eigvecs := massEigenvectorBasis d N a mass
  set eigvals := massEigenvalues d N a mass
  set enum := Fintype.equivFin (FinLatticeSites d N)
  -- Define the underlying linear map
  set L : FinLatticeField d N →ₗ[ℝ] ell2' :=
    { toFun := fun f => ∑ k : FinLatticeSites d N,
        ((Real.sqrt (eigvals k))⁻¹ *
         ∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * f x) •
        lp.single 2 (enum k).val (1 : ℝ)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r f
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [smul_smul]
        congr 1
        calc
          (Real.sqrt (eigvals k))⁻¹ *
              (∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * (r * f x))
              = (Real.sqrt (eigvals k))⁻¹ *
                  (r * ∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                    congr 1
                    calc
                      (∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * (r * f x))
                          = ∑ x : FinLatticeSites d N,
                              r * ((eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                                apply Finset.sum_congr rfl
                                intro x hx
                                ring
                      _ = r * ∑ x : FinLatticeSites d N,
                            (eigvecs k : EuclideanSpace ℝ _) x * f x := by
                              rw [Finset.mul_sum]
          _ = r * ((Real.sqrt (eigvals k))⁻¹ *
                  ∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                    ring }
  -- Any linear map from a finite-dimensional space to a normed space is continuous
  exact { L with cont := L.continuous_of_finiteDimensional }

/-- Key identity: `⟨Tf, Tg⟩_ℓ² = ∑ x, f(x) · (Q⁻¹g)(x)` where `Q⁻¹g`
is the inverse mass operator applied to g.

Equivalently: `⟨Tf, Tg⟩ = Σ_k λ_k⁻¹ · c_k(f) · c_k(g)`
where `c_k(f) = ⟪e_k, f⟫_L²` and `λ_k` are eigenvalues of Q. -/
theorem spectralLatticeCovariance_inner (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    @inner ℝ ell2' _
      (spectralLatticeCovariance d N a mass ha hmass f)
      (spectralLatticeCovariance d N a mass ha hmass g) =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
  let enum : FinLatticeSites d N ≃ Fin (Fintype.card (FinLatticeSites d N)) :=
    Fintype.equivFin (FinLatticeSites d N)
  let lam : FinLatticeSites d N → ℝ := massEigenvalues d N a mass
  let s : FinLatticeSites d N → ℝ := fun k =>
    ∑ x : FinLatticeSites d N, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x
  let t : FinLatticeSites d N → ℝ := fun k =>
    ∑ x : FinLatticeSites d N, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x
  have hlam : ∀ k : FinLatticeSites d N, 0 < lam k := by
    intro k
    simpa [lam] using massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k
  have hf :
      spectralLatticeCovariance d N a mass ha hmass f =
      ∑ k : FinLatticeSites d N,
        ((Real.sqrt (lam k))⁻¹ * s k) • lp.single 2 (enum k).val (1 : ℝ) := by
    unfold spectralLatticeCovariance
    simp [enum, lam, s]
  have hg :
      spectralLatticeCovariance d N a mass ha hmass g =
      ∑ k : FinLatticeSites d N,
        ((Real.sqrt (lam k))⁻¹ * t k) • lp.single 2 (enum k).val (1 : ℝ) := by
    unfold spectralLatticeCovariance
    simp [enum, lam, t]
  rw [hf, hg]
  simp [inner_sum, sum_inner, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hleft :
      ∑ i,
        inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) •
          lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
          (((Real.sqrt (lam k))⁻¹ * t k) •
            lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) =
      ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k) := by
    classical
    simpa using (show ∑ i : FinLatticeSites d N,
      inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
        (((Real.sqrt (lam k))⁻¹ * t k) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ))
      = ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k) from by
        classical
        rw [Finset.sum_eq_single k]
        · have hsingle : inner ℝ (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ))
              (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 1 := by
              simp
          simp [inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
        · intro i hi hik
          have hne : enum i ≠ enum k := by
            intro h; exact hik (enum.injective h)
          have : inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
              (((Real.sqrt (lam k))⁻¹ * t k) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 0 := by
                have hne_val : (enum i).val ≠ (enum k).val := by
                  intro h
                  apply hne
                  exact Fin.ext h
                have hsingle0 :
                    inner ℝ (lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
                      (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 0 := by
                  rw [lp.inner_single_left]
                  simp [lp.single_apply, hne_val]
                simp [inner_smul_left, inner_smul_right, hsingle0, mul_comm]
          exact this
        · intro hknot
          exact (hknot (Finset.mem_univ k)).elim)
  have hrhs :
      (∑ x, ∑ i,
        (massEigenvalues d N a mass k)⁻¹ *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) i * f i) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x)) =
      (lam k)⁻¹ * s k * t k := by
    calc
      (∑ x, ∑ i,
        (massEigenvalues d N a mass k)⁻¹ *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) i * f i) *
          ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x))
          = ∑ i, ∑ x,
              (massEigenvalues d N a mass k)⁻¹ *
                ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) i * f i) *
                ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
              rw [Finset.sum_comm]
      _ = (lam k)⁻¹ *
            (∑ i, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) i * f i) *
            (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
              simp [lam, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = (lam k)⁻¹ * s k * t k := by simp [s, t]
  rw [hleft, hrhs]
  have hsq : Real.sqrt (lam k) * Real.sqrt (lam k) = lam k := by
    nlinarith [Real.sq_sqrt (le_of_lt (hlam k))]
  calc
    ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k)
        = (((Real.sqrt (lam k))⁻¹ * (Real.sqrt (lam k))⁻¹) * s k) * t k := by ring
    _ = (((Real.sqrt (lam k) * Real.sqrt (lam k))⁻¹) * s k) * t k := by ring
    _ = (lam k)⁻¹ * s k * t k := by simp [hsq]

/-- The ℓ² norm squared of `Tf` equals the quadratic form `⟨f, Q⁻¹f⟩_L²`.
This is `spectralLatticeCovariance_inner` with `g = f`. -/
theorem spectralLatticeCovariance_norm_sq (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    @inner ℝ ell2' _
      (spectralLatticeCovariance d N a mass ha hmass f)
      (spectralLatticeCovariance d N a mass ha hmass f) =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
  rw [spectralLatticeCovariance_inner]
  congr 1; ext k; ring

/-- Bridge between spectral form and site-basis bilinear form:
`Σ_k λ_k⁻¹ c_k(f) c_k(g) = Σ_x f(x) (Q⁻¹ g)(x)`.

The LHS is the spectral decomposition of `⟨f, Q⁻¹g⟩`; the RHS is its
site-basis expansion. These are equal by the completeness of the eigenbasis. -/
theorem spectral_eq_site_bilinear (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) =
    ∑ x, f x *
      (∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
        (∑ y, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y) *
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) := by
  let A : FinLatticeSites d N → ℝ := fun k => (massEigenvalues d N a mass k)⁻¹
  let B : FinLatticeSites d N → FinLatticeSites d N → ℝ :=
    fun k x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x
  let C : FinLatticeSites d N → ℝ := fun k => ∑ y, B k y * g y
  calc
    ∑ k : FinLatticeSites d N, A k * (∑ x, B k x * f x) * C k
        = ∑ k : FinLatticeSites d N, ∑ x, f x * (A k * C k * B k x) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            have hsum : (∑ x, B k x * f x) = ∑ x, f x * B k x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
            rw [hsum]
            calc
              A k * (∑ x : FinLatticeSites d N, f x * B k x) * C k
                  = (A k * C k) * (∑ x : FinLatticeSites d N, f x * B k x) := by ring
              _ = ∑ x : FinLatticeSites d N, (A k * C k) * (f x * B k x) := by
                    rw [Finset.mul_sum]
              _ = ∑ x : FinLatticeSites d N, f x * (A k * C k * B k x) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    ring
    _ = ∑ x : FinLatticeSites d N, ∑ k, f x * (A k * C k * B k x) := by
          rw [Finset.sum_comm]
    _ = ∑ x : FinLatticeSites d N, f x * (∑ k, A k * C k * B k x) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [← Finset.mul_sum]
    _ = ∑ x, f x *
          (∑ k : FinLatticeSites d N, A k * C k * B k x) := rfl
    _ = ∑ x, f x *
          (∑ k : FinLatticeSites d N,
            (massEigenvalues d N a mass k)⁻¹ *
            (∑ y, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y) *
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) := by
          simp [A, B, C]

/-- The bounded sequence condition for the spectral singular values.
Needed to show the CLM maps into ℓ². -/
theorem spectral_singular_values_bounded (a mass : ℝ)
    (_ha : 0 < a) (_hmass : 0 < mass) :
    IsBoundedSeq (fun m =>
      if h : m < Fintype.card (FinLatticeSites d N) then
        Real.sqrt ((massEigenvalues d N a mass
          ((Fintype.equivFin _).symm ⟨m, h⟩))⁻¹)
      else 0) := by
  let n := Fintype.card (FinLatticeSites d N)
  let σ : ℕ → ℝ := fun m =>
    if h : m < n then
      Real.sqrt ((massEigenvalues d N a mass
        ((Fintype.equivFin _).symm ⟨m, h⟩))⁻¹)
    else 0
  change IsBoundedSeq σ
  unfold IsBoundedSeq
  refine ⟨Finset.sum (Finset.range n) (fun i => |σ i|), ?_⟩
  intro m
  by_cases hm : m < n
  · have hm_mem : m ∈ Finset.range n := Finset.mem_range.mpr hm
    exact Finset.single_le_sum (fun i _ => abs_nonneg (σ i)) hm_mem
  · have hsum_nonneg : 0 ≤ Finset.sum (Finset.range n) (fun i => |σ i|) :=
      Finset.sum_nonneg (fun i _ => abs_nonneg (σ i))
    simpa [σ, hm] using hsum_nonneg

/-! ## Gaussian density

Defined here (rather than in FKG.lean) so that Density.lean can access it
without circular imports. -/

/-- The Gaussian density on `FinLatticeField d N` (unnormalized):
`ρ(φ) = exp(-½ ⟨φ, Qφ⟩)` where Q = -Δ_a + m² is the mass operator. -/
def gaussianDensity (a mass : ℝ)
    (φ : FinLatticeField d N) : ℝ :=
  Real.exp (-(1/2) * ∑ x : FinLatticeSites d N,
    φ x * (massOperator d N a mass φ) x)

/-- Spectral form of the Gaussian density exponent. -/
theorem gaussianDensity_eq_exp_spectral (a mass : ℝ)
    (φ : FinLatticeField d N) :
    gaussianDensity d N a mass φ =
      Real.exp (-(1 / 2 : ℝ) *
        ∑ k : FinLatticeSites d N,
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x) ^ 2) := by
  unfold gaussianDensity
  rw [massOperator_quadratic_eq_spectral (d := d) (N := N) a mass φ]

/-- Coefficient extraction after reconstructing from eigenbasis coordinates. -/
theorem massEigenbasis_coeff_reprSymm (a mass : ℝ)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) (k : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N,
      (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
        ((massEigenvectorBasis d N a mass).repr.symm v) x) = v k := by
  have hrepr := OrthonormalBasis.repr_apply_apply
    (b := massEigenvectorBasis d N a mass)
    (v := (massEigenvectorBasis d N a mass).repr.symm v) (i := k)
  have hleft :
      ((massEigenvectorBasis d N a mass).repr
        ((massEigenvectorBasis d N a mass).repr.symm v)).ofLp k = v k := by
    simpa using congrArg (fun w => w k) (LinearEquiv.apply_symm_apply
      (massEigenvectorBasis d N a mass).repr v)
  have hright :
      inner ℝ (massEigenvectorBasis d N a mass k)
        ((massEigenvectorBasis d N a mass).repr.symm v) =
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          ((massEigenvectorBasis d N a mass).repr.symm v) x) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  rw [hright] at hrepr
  exact (hleft.symm.trans hrepr).symm

/-- Quadratic spectral sum is unchanged under reconstructing from eigenbasis
coordinates. -/
theorem massEigenbasis_quadratic_sum_reprSymm (a mass : ℝ)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) :
    (∑ k : FinLatticeSites d N,
      massEigenvalues d N a mass k *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            ((massEigenvectorBasis d N a mass).repr.symm v) x) ^ 2) =
    ∑ k : FinLatticeSites d N, massEigenvalues d N a mass k * (v k) ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [massEigenbasis_coeff_reprSymm (d := d) (N := N) a mass v k]

/-- Linear spectral sum is unchanged under reconstructing from eigenbasis
coordinates. -/
theorem massEigenbasis_linear_sum_reprSymm (a mass : ℝ)
    (c : FinLatticeField d N)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) :
    (∑ k : FinLatticeSites d N, c k *
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          ((massEigenvectorBasis d N a mass).repr.symm v) x)) =
    ∑ k : FinLatticeSites d N, c k * v k := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [massEigenbasis_coeff_reprSymm (d := d) (N := N) a mass v k]

/-- `ofLp` version of `massEigenbasis_coeff_reprSymm`. -/
theorem massEigenbasis_coeff_reprSymm_ofLp (a mass : ℝ)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) (k : FinLatticeSites d N) :
    (∑ x : FinLatticeSites d N,
      (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
        ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x) = v.ofLp k := by
  simpa using massEigenbasis_coeff_reprSymm (d := d) (N := N) a mass v k

/-- `ofLp` version of `massEigenbasis_quadratic_sum_reprSymm`. -/
theorem massEigenbasis_quadratic_sum_reprSymm_ofLp (a mass : ℝ)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) :
    (∑ k : FinLatticeSites d N,
      massEigenvalues d N a mass k *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
            ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x) ^ 2) =
    ∑ k : FinLatticeSites d N, massEigenvalues d N a mass k * (v.ofLp k) ^ 2 := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [massEigenbasis_coeff_reprSymm_ofLp (d := d) (N := N) a mass v k]

/-- `ofLp` version of `massEigenbasis_linear_sum_reprSymm`. -/
theorem massEigenbasis_linear_sum_reprSymm_ofLp (a mass : ℝ)
    (c : FinLatticeField d N)
    (v : EuclideanSpace ℝ (FinLatticeSites d N)) :
    (∑ k : FinLatticeSites d N, c k *
      (∑ x : FinLatticeSites d N,
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x)) =
    ∑ k : FinLatticeSites d N, c k * v.ofLp k := by
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [massEigenbasis_coeff_reprSymm_ofLp (d := d) (N := N) a mass v k]

/-- The Gaussian density is non-negative. -/
theorem gaussianDensity_nonneg (a mass : ℝ) (φ : FinLatticeField d N) :
    0 ≤ gaussianDensity d N a mass φ :=
  le_of_lt (Real.exp_pos _)

end GaussianField
