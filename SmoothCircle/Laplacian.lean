/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Laplacian on the Circle S¹_L

Defines the Laplacian `-d²/dx²` as a continuous linear map on `SmoothMap_Circle L ℝ`
and proves it acts on the Fourier basis by eigenvalue multiplication.

## Main definitions

- `circleLaplacian L` — CLM: `SmoothMap_Circle L ℝ →L[ℝ] SmoothMap_Circle L ℝ`

## Main results

- `circleLaplacian_fourierBasis` — eigenvalue equation:
  `(-d²/dx²)(ψ_n) = λ_n · ψ_n` where `λ_n = (2πk/L)²`

## References

- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II
- Stein-Shakarchi, *Fourier Analysis*, Ch. 3
-/

import SmoothCircle.Eigenvalues

noncomputable section

namespace GaussianField

open SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## The derivative as a CLM on smooth periodic functions

The derivative `d/dx` maps smooth periodic functions to smooth periodic functions.
We prove it is a continuous linear map via the Sobolev bound `p_k(f') ≤ p_{k+1}(f)`. -/

/-- The derivative of a smooth periodic function is smooth and periodic. -/
def derivSC (f : SmoothMap_Circle L ℝ) : SmoothMap_Circle L ℝ where
  toFun := deriv f
  periodic' := by
    have h := f.periodic_iteratedDeriv 1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h; exact h
  smooth' := (contDiff_infty_iff_deriv.mp f.smooth).2

@[simp] theorem derivSC_apply (f : SmoothMap_Circle L ℝ) (x : ℝ) :
    (derivSC L f) x = deriv f x := rfl

theorem derivSC_add (f g : SmoothMap_Circle L ℝ) :
    derivSC L (f + g) = derivSC L f + derivSC L g := by
  ext x
  simp only [derivSC_apply, add_apply]
  have hf := (f.contDiffAt_of_smooth 1 x).differentiableAt_one
  have hg := (g.contDiffAt_of_smooth 1 x).differentiableAt_one
  exact deriv_add hf hg

theorem derivSC_smul (r : ℝ) (f : SmoothMap_Circle L ℝ) :
    derivSC L (r • f) = r • derivSC L f := by
  ext x
  simp only [derivSC_apply, smul_apply]
  have hf := (f.contDiffAt_of_smooth 1 x).differentiableAt_one
  exact deriv_const_smul r hf

/-- The derivative as a linear map on smooth periodic functions. -/
def derivSCLM : SmoothMap_Circle L ℝ →ₗ[ℝ] SmoothMap_Circle L ℝ where
  toFun := derivSC L
  map_add' := derivSC_add L
  map_smul' := derivSC_smul L

/-- The derivative is continuous: `p_k(f') ≤ p_{k+1}(f)`. -/
theorem derivSC_continuous : Continuous (derivSCLM L : SmoothMap_Circle L ℝ →ₗ[ℝ] _) := by
  apply WithSeminorms.continuous_of_isBounded
    smoothCircle_withSeminorms smoothCircle_withSeminorms
  intro k
  refine ⟨{k + 1}, ⟨⟨1, by norm_num⟩, fun f => ?_⟩⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, Seminorm.smul_apply,
    NNReal.smul_def, derivSCLM]
  -- p_k(f') = sup |f'^(k)(x)| = sup |f^(k+1)(x)| = p_{k+1}(f)
  apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
  rintro _ ⟨x, hx, rfl⟩
  -- iteratedDeriv k (deriv f) = iteratedDeriv (k+1) f
  have eq : iteratedDeriv k (deriv (⇑f)) x = iteratedDeriv (k + 1) (⇑f) x := by
    rw [iteratedDeriv_succ']
  have : iteratedDeriv k (⇑(derivSC L f)) x = iteratedDeriv (k + 1) (⇑f) x := eq
  have bound := norm_iteratedDeriv_le_sobolevSeminorm f (k + 1) hx
  convert bound using 1
  · -- beta reduce and use iteratedDeriv k (derivSC f) = iteratedDeriv (k+1) f
    show ‖iteratedDeriv k (⇑(derivSC L f)) x‖ = ‖iteratedDeriv (k + 1) (⇑f) x‖
    rw [this]
  · -- ⟨1, _⟩ • p = p
    show (⟨1, _⟩ : NNReal) • (sobolevSeminorm (k + 1)) f = _
    exact one_smul _ _

/-- The derivative as a CLM on smooth periodic functions. -/
def derivSCCLM : SmoothMap_Circle L ℝ →L[ℝ] SmoothMap_Circle L ℝ where
  toLinearMap := derivSCLM L
  cont := derivSC_continuous L

/-! ## Laplacian as CLM -/

/-- **The Laplacian on S¹_L.**

  `(-d²/dx²)(f)(x) = -f''(x)`

Defined as the composition `-derivSCCLM ∘ derivSCCLM`. -/
def circleLaplacian : SmoothMap_Circle L ℝ →L[ℝ] SmoothMap_Circle L ℝ :=
  -(derivSCCLM L).comp (derivSCCLM L)

theorem circleLaplacian_apply (f : SmoothMap_Circle L ℝ) (x : ℝ) :
    (circleLaplacian L f) x = -(deriv (deriv f) x) := by
  simp [circleLaplacian, derivSCCLM, derivSCLM, derivSC, neg_apply]

/-! ## Derivatives of Fourier basis functions

We compute the second derivatives of the real Fourier basis using `HasDerivAt`
for trig functions composed with linear maps. -/

/-- The angular frequency of the k-th Fourier mode. -/
private def fourierOmega (k : ℕ) : ℝ := 2 * Real.pi * k / L

/-- `HasDerivAt` for the linear phase `x ↦ 2πkx/L`. -/
private theorem hasDerivAt_fourierPhase (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => 2 * Real.pi * (k : ℝ) * x / L) (fourierOmega L k) x := by
  have h : (fun x => 2 * Real.pi * (k : ℝ) * x / L) = (fun x => fourierOmega L k * x) := by
    ext y; simp [fourierOmega]; ring
  rw [h]
  simpa using (hasDerivAt_id x).const_mul (fourierOmega L k)

/-- First derivative of `A · cos(2πkx/L)`. -/
private theorem hasDerivAt_cos_phase (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => Real.sqrt (2 / L) * Real.cos (2 * Real.pi * (k : ℝ) * x / L))
      (-Real.sqrt (2 / L) * fourierOmega L k *
        Real.sin (2 * Real.pi * (k : ℝ) * x / L)) x := by
  have h1 := (Real.hasDerivAt_cos (2 * Real.pi * (k : ℝ) * x / L)).comp x
    (hasDerivAt_fourierPhase L k x)
  convert (hasDerivAt_const x (Real.sqrt (2 / L))).mul h1 using 1
  ring

/-- First derivative of `A · sin(2πkx/L)`. -/
private theorem hasDerivAt_sin_phase (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => Real.sqrt (2 / L) * Real.sin (2 * Real.pi * (k : ℝ) * x / L))
      (Real.sqrt (2 / L) * fourierOmega L k *
        Real.cos (2 * Real.pi * (k : ℝ) * x / L)) x := by
  have h1 := (Real.hasDerivAt_sin (2 * Real.pi * (k : ℝ) * x / L)).comp x
    (hasDerivAt_fourierPhase L k x)
  convert (hasDerivAt_const x (Real.sqrt (2 / L))).mul h1 using 1
  ring

/-- Second derivative of `A · cos(2πkx/L)`. -/
private theorem hasDerivAt_deriv_cos (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => -Real.sqrt (2 / L) * fourierOmega L k *
        Real.sin (2 * Real.pi * (k : ℝ) * x / L))
      (-Real.sqrt (2 / L) * (fourierOmega L k) ^ 2 *
        Real.cos (2 * Real.pi * (k : ℝ) * x / L)) x := by
  convert (hasDerivAt_sin_phase L k x).const_mul (-fourierOmega L k) using 1 <;> ring

/-- Second derivative of `A · sin(2πkx/L)`. -/
private theorem hasDerivAt_deriv_sin (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => Real.sqrt (2 / L) * fourierOmega L k *
        Real.cos (2 * Real.pi * (k : ℝ) * x / L))
      (-Real.sqrt (2 / L) * (fourierOmega L k) ^ 2 *
        Real.sin (2 * Real.pi * (k : ℝ) * x / L)) x := by
  convert (hasDerivAt_cos_phase L k x).const_mul (fourierOmega L k) using 1 <;> ring

/-! ## Eigenvalue equation -/

/-- Helper: two successive `HasDerivAt` steps determine `deriv (deriv f)`. -/
private theorem deriv_deriv_eq_of_hasDerivAt {f f' : ℝ → ℝ} {f'' : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : HasDerivAt f' f'' x) :
    deriv (deriv f) x = f'' := by
  have h1 : deriv f = f' := funext (fun y => (hf y).deriv)
  rw [h1]
  exact hf'.deriv

/-- Eigenvalue formula: (2πk/L)² = 4π²k²/L². -/
private theorem eigenvalue_formula (k : ℕ) :
    (2 * Real.pi * (k : ℝ) / L) ^ 2 = 4 * Real.pi ^ 2 * (k : ℝ) ^ 2 / L ^ 2 := by
  ring

/-- The Laplacian acts on the n-th Fourier basis function by eigenvalue multiplication.

  `(-d²/dx²)(ψ_n)(x) = (2πk/L)² · ψ_n(x)` where `k = fourierFreq(n)`. -/
theorem circleLaplacian_fourierBasis (n : ℕ) :
    circleLaplacian L (SmoothMap_Circle.fourierBasis n) =
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) n •
      SmoothMap_Circle.fourierBasis n := by
  ext x
  rw [circleLaplacian_apply]
  simp only [smul_apply, SmoothMap_Circle.fourierBasis_apply]
  -- Unfold eigenvalue
  show -(deriv (deriv (fourierBasisFun (L := L) n)) x) =
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) n *
      fourierBasisFun (L := L) n x
  cases n with
  | zero =>
    -- Constant mode: both derivatives are 0
    simp only [fourierBasisFun]
    -- deriv of constant = 0, so deriv(deriv(const)) = deriv(0) = 0
    have h1 : deriv (fun (_ : ℝ) => (1 : ℝ) / Real.sqrt L) = fun _ => 0 :=
      funext (fun x => deriv_const x _)
    rw [h1, deriv_const]
    simp [HasLaplacianEigenvalues.eigenvalue, fourierFreq]
  | succ m =>
    simp only [fourierBasisFun]
    set k := m / 2 + 1
    split
    · -- Cosine case
      rw [deriv_deriv_eq_of_hasDerivAt (hasDerivAt_cos_phase L k)
        (hasDerivAt_deriv_cos L k x)]
      simp only [HasLaplacianEigenvalues.eigenvalue, fourierOmega]
      have hk : k = SmoothMap_Circle.fourierFreq (1 + m) := by
        simp only [SmoothMap_Circle.fourierFreq, Nat.add_comm 1 m]; rfl
      rw [hk]
      ring
    · -- Sine case
      rw [deriv_deriv_eq_of_hasDerivAt (hasDerivAt_sin_phase L k)
        (hasDerivAt_deriv_sin L k x)]
      simp only [HasLaplacianEigenvalues.eigenvalue, fourierOmega]
      have hk : k = SmoothMap_Circle.fourierFreq (1 + m) := by
        simp only [SmoothMap_Circle.fourierFreq, Nat.add_comm 1 m]; rfl
      rw [hk]
      ring

end GaussianField
