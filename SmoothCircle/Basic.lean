/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth Periodic Functions on the Circle

Defines `SmoothCircle L`, the space of L-periodic smooth functions `ℝ → ℝ`,
equipped with Sobolev sup-seminorms and a real Fourier basis.

## Main definitions

- `SmoothCircle L` — L-periodic smooth functions
- `SmoothCircle.sobolevSeminorm k` — the k-th Sobolev sup-norm: `sup_{x ∈ [0,L]} |f^(k)(x)|`
- `SmoothCircle.fourierBasis n` — orthonormal real Fourier basis indexed by ℕ
- `SmoothCircle.fourierCoeffReal n` — real Fourier coefficient functionals

## Mathematical background

The space C∞(S¹) of smooth L-periodic functions is a nuclear Fréchet space
with topology given by the family of Sobolev sup-norms
`p_k(f) = sup_{x ∈ [0,L]} |f^(k)(x)|`. The real Fourier basis
`{1/√L, √(2/L)·cos(2πnx/L), √(2/L)·sin(2πnx/L)}` provides a Schauder
basis with polynomial growth and rapid coefficient decay.
-/

import Nuclear.NuclearTensorProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace GaussianField

/-! ## SmoothCircle type definition -/

/-- An L-periodic smooth function `ℝ → ℝ`. Elements represent smooth functions
on the circle `ℝ/Lℤ`, stored as periodic functions on `ℝ` for calculus convenience. -/
structure SmoothCircle (L : ℝ) [Fact (0 < L)] where
  toFun : ℝ → ℝ
  periodic' : Function.Periodic toFun L
  smooth' : ContDiff ℝ ⊤ toFun

variable {L : ℝ} [hL : Fact (0 < L)]

namespace SmoothCircle

/-! ### Function-like structure -/

instance instFunLike : FunLike (SmoothCircle L) ℝ ℝ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : SmoothCircle L} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem coe_mk (f : ℝ → ℝ) (hp : Function.Periodic f L)
    (hs : ContDiff ℝ ⊤ f) : (SmoothCircle.mk f hp hs : ℝ → ℝ) = f := rfl

theorem periodic (f : SmoothCircle L) : Function.Periodic f L := f.periodic'

theorem smooth (f : SmoothCircle L) : ContDiff ℝ ⊤ f := f.smooth'

theorem continuous (f : SmoothCircle L) : Continuous f := f.smooth.continuous

theorem contDiffAt_of_smooth (f : SmoothCircle L) (k : ℕ) (x : ℝ) :
    ContDiffAt ℝ (↑k) f x :=
  (f.smooth.of_le le_top).contDiffAt

/-! ### Algebraic structure -/

instance instZero : Zero (SmoothCircle L) :=
  ⟨⟨0, fun _ => rfl, contDiff_const⟩⟩

@[simp] theorem coe_zero : (↑(0 : SmoothCircle L) : ℝ → ℝ) = 0 := rfl
@[simp] theorem zero_apply (x : ℝ) : (0 : SmoothCircle L) x = 0 := rfl

private theorem periodic_add (f g : SmoothCircle L) :
    Function.Periodic (f + g : ℝ → ℝ) L :=
  fun x => show f (x + L) + g (x + L) = f x + g x by
    rw [f.periodic x, g.periodic x]

instance instAdd : Add (SmoothCircle L) :=
  ⟨fun f g => ⟨f + g, periodic_add f g, f.smooth.add g.smooth⟩⟩

@[simp] theorem add_apply (f g : SmoothCircle L) (x : ℝ) : (f + g) x = f x + g x := rfl

private theorem periodic_neg (f : SmoothCircle L) :
    Function.Periodic (fun x => -f x) L :=
  fun x => show -f (x + L) = -f x by rw [f.periodic x]

instance instNeg : Neg (SmoothCircle L) :=
  ⟨fun f => ⟨fun x => -f x, periodic_neg f, f.smooth.neg⟩⟩

@[simp] theorem neg_apply (f : SmoothCircle L) (x : ℝ) : (-f) x = -f x := rfl

private theorem periodic_sub (f g : SmoothCircle L) :
    Function.Periodic (fun x => f x - g x) L :=
  fun x => show f (x + L) - g (x + L) = f x - g x by
    rw [f.periodic x, g.periodic x]

instance instSub : Sub (SmoothCircle L) :=
  ⟨fun f g => ⟨fun x => f x - g x, periodic_sub f g, f.smooth.sub g.smooth⟩⟩

private theorem periodic_smul (r : ℝ) (f : SmoothCircle L) :
    Function.Periodic (fun x => r * f x) L :=
  fun x => show r * f (x + L) = r * f x by rw [f.periodic x]

instance instSMul : SMul ℝ (SmoothCircle L) :=
  ⟨fun r f => ⟨fun x => r * f x, periodic_smul r f, f.smooth.const_smul r⟩⟩

@[simp] theorem smul_apply (r : ℝ) (f : SmoothCircle L) (x : ℝ) :
    (r • f) x = r * f x := rfl

instance instAddCommGroup : AddCommGroup (SmoothCircle L) where
  add_assoc f g h := ext fun x => add_assoc _ _ _
  zero_add f := ext fun x => zero_add _
  add_zero f := ext fun x => add_zero _
  neg_add_cancel f := ext fun x => neg_add_cancel _
  add_comm f g := ext fun x => add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SmoothCircle L) where
  one_smul f := ext fun x => one_mul _
  mul_smul r s f := ext fun x => mul_assoc _ _ _
  smul_zero r := ext fun x => mul_zero _
  smul_add r f g := ext fun x => mul_add _ _ _
  add_smul r s f := ext fun x => add_mul _ _ _
  zero_smul f := ext fun x => zero_mul _

/-! ### Iterated derivatives of smooth periodic functions -/

/-- The k-th derivative of a smooth periodic function is continuous. -/
theorem continuous_iteratedDeriv (f : SmoothCircle L) (k : ℕ) :
    Continuous (iteratedDeriv k f) :=
  f.smooth.continuous_iteratedDeriv k le_top

/-- The k-th derivative of a smooth periodic function is periodic.
Proof: by induction on k, using that the derivative of a periodic
differentiable function is periodic. -/
theorem periodic_iteratedDeriv (f : SmoothCircle L) (k : ℕ) :
    Function.Periodic (iteratedDeriv k f) L := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using f.periodic
  | succ n ih =>
    intro x
    -- iteratedDeriv (n+1) f = deriv (iteratedDeriv n f)
    rw [iteratedDeriv_succ]
    -- We need: deriv (iteratedDeriv n f) (x + L) = deriv (iteratedDeriv n f) x
    -- This follows because iteratedDeriv n f is periodic (IH) and differentiable
    set g := iteratedDeriv n (⇑f) with hg_def
    -- g is periodic by IH, and smooth (hence differentiable)
    have hg_diff : ∀ y, DifferentiableAt ℝ g y :=
      fun y => (f.smooth.differentiable_iteratedDeriv n (WithTop.coe_lt_top _)).differentiableAt
    -- deriv g (x + L) = deriv (g ∘ (· + L)) x = deriv g x (by periodicity g ∘ (· + L) = g)
    have h1 : (fun y => g (y + L)) = g := funext (fun y => ih y)
    have key : deriv g (x + L) = deriv (fun y => g (y + L)) x := by
      have hcomp := deriv.scomp x (hg_diff (x + L))
        (differentiableAt_id.add (differentiableAt_const L))
      simp at hcomp
      have : g ∘ (id + fun _ => L) = (fun y => g (y + L)) := by ext; simp
      rw [this] at hcomp
      exact hcomp.symm
    rw [key, h1]

/-- The norm of the k-th derivative is bounded on [0, L] (compact + continuous). -/
theorem bddAbove_norm_iteratedDeriv_image (f : SmoothCircle L) (k : ℕ) :
    BddAbove ((fun x => ‖iteratedDeriv k f x‖) '' Set.Icc 0 L) :=
  (isCompact_Icc.image (f.continuous_iteratedDeriv k).norm).bddAbove

/-- [0, L] is nonempty when L > 0. -/
theorem Icc_nonempty : (Set.Icc (0 : ℝ) L).Nonempty :=
  Set.nonempty_Icc.mpr (le_of_lt hL.out)

/-! ### Sobolev sup-seminorms -/

/-- The Sobolev sup-seminorm: `p_k(f) = sup_{x ∈ [0,L]} ‖f^(k)(x)‖`. -/
def sobolevSeminorm (k : ℕ) : Seminorm ℝ (SmoothCircle L) where
  toFun f := sSup ((fun x => ‖iteratedDeriv k f x‖) '' Set.Icc 0 L)
  map_zero' := by
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedDeriv_fun_const_zero]
    · exact le_csSup_of_le
        ((0 : SmoothCircle L).bddAbove_norm_iteratedDeriv_image k)
        ⟨0, Set.left_mem_Icc.mpr (le_of_lt hL.out), rfl⟩
        (by simp [iteratedDeriv_fun_const_zero])
  add_le' f g := by
    apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
    rintro _ ⟨x, hx, rfl⟩
    have hf_le := le_csSup (f.bddAbove_norm_iteratedDeriv_image k)
      ⟨x, hx, rfl⟩
    have hg_le := le_csSup (g.bddAbove_norm_iteratedDeriv_image k)
      ⟨x, hx, rfl⟩
    calc ‖iteratedDeriv k (↑(f + g)) x‖
        = ‖iteratedDeriv k f x + iteratedDeriv k g x‖ := by
          congr 1
          exact iteratedDeriv_add (f.contDiffAt_of_smooth k x) (g.contDiffAt_of_smooth k x)
      _ ≤ ‖iteratedDeriv k f x‖ + ‖iteratedDeriv k g x‖ := norm_add_le _ _
      _ ≤ sSup ((fun x => ‖iteratedDeriv k f x‖) '' Set.Icc 0 L) +
          sSup ((fun x => ‖iteratedDeriv k g x‖) '' Set.Icc 0 L) :=
          add_le_add hf_le hg_le
  neg' f := by
    -- (-f : SmoothCircle L) coerces to -(↑f : ℝ → ℝ) definitionally.
    -- iteratedDeriv_neg then gives iteratedDeriv k (-↑f) x = -(iteratedDeriv k ↑f x),
    -- and norm_neg gives ‖-(iteratedDeriv k ↑f x)‖ = ‖iteratedDeriv k ↑f x‖.
    have hcoe : ((-f : SmoothCircle L) : ℝ → ℝ) = -(↑f : ℝ → ℝ) := rfl
    simp_rw [hcoe, iteratedDeriv_neg, norm_neg]
  smul' r f := by
    -- (r • f : SmoothCircle L) coerces to r • (↑f : ℝ → ℝ) (pointwise scalar multiplication).
    -- iteratedDeriv_const_smul_field gives iteratedDeriv k (r • ↑f) x = r • iteratedDeriv k ↑f x,
    -- and norm_smul gives ‖r • iteratedDeriv k ↑f x‖ = ‖r‖ * ‖iteratedDeriv k ↑f x‖.
    -- Finally, sSup of {‖r‖ * y | y ∈ S} = ‖r‖ * sSup S by Real.sSup_smul_of_nonneg.
    have hcoe : ((r • f : SmoothCircle L) : ℝ → ℝ) = r • (↑f : ℝ → ℝ) := by
      ext x; simp [smul_apply]
    simp_rw [hcoe, iteratedDeriv_const_smul_field, norm_smul]
    open Pointwise in
    rw [show (fun x => ‖r‖ * ‖iteratedDeriv k (↑f : ℝ → ℝ) x‖) '' Set.Icc 0 L =
         ‖r‖ • ((fun x => ‖iteratedDeriv k (↑f : ℝ → ℝ) x‖) '' Set.Icc 0 L) from ?_]
    · rw [Real.sSup_smul_of_nonneg (norm_nonneg r), smul_eq_mul]
    · ext x; simp [Set.mem_image, Set.mem_smul_set, smul_eq_mul]

/-- The Sobolev seminorm is nonneg. -/
theorem sobolevSeminorm_nonneg (k : ℕ) (f : SmoothCircle L) :
    0 ≤ sobolevSeminorm k f :=
  le_csSup_of_le (f.bddAbove_norm_iteratedDeriv_image k)
    ⟨0, Set.left_mem_Icc.mpr (le_of_lt hL.out), rfl⟩
    (norm_nonneg _)

/-- Pointwise bound: `‖f^(k)(x)‖ ≤ p_k(f)` for `x ∈ [0, L]`. -/
theorem norm_iteratedDeriv_le_sobolevSeminorm (f : SmoothCircle L) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc 0 L) :
    ‖iteratedDeriv k f x‖ ≤ sobolevSeminorm k f :=
  le_csSup (f.bddAbove_norm_iteratedDeriv_image k) ⟨x, hx, rfl⟩

/-- Pointwise bound for any x (by periodicity). -/
theorem norm_iteratedDeriv_le_sobolevSeminorm' (f : SmoothCircle L) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k f x‖ ≤ sobolevSeminorm k f := by
  set g := iteratedDeriv k (⇑f)
  set y := toIcoMod hL.out 0 x
  have hmod := toIcoMod_mem_Ico hL.out (0 : ℝ) x
  have hy_mem : y ∈ Set.Icc 0 L := by
    refine ⟨hmod.1, ?_⟩; have := hmod.2; simp at this; linarith
  have hper := f.periodic_iteratedDeriv k
  have heq : g x = g y := by
    show g x = g (toIcoMod hL.out 0 x)
    conv_lhs => rw [← toIcoMod_add_toIcoDiv_zsmul hL.out 0 x]
    exact (hper.zsmul _) _
  rw [heq]
  exact norm_iteratedDeriv_le_sobolevSeminorm f k hy_mem

/-! ### Topology from seminorms -/

instance instTopologicalSpace : TopologicalSpace (SmoothCircle L) :=
  (SeminormFamily.moduleFilterBasis
    (𝕜 := ℝ) (sobolevSeminorm (L := L))).topology

theorem smoothCircle_withSeminorms :
    WithSeminorms (sobolevSeminorm : ℕ → Seminorm ℝ (SmoothCircle L)) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (SmoothCircle L) :=
  smoothCircle_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ (SmoothCircle L) :=
  smoothCircle_withSeminorms.continuousSMul

/-! ### Real Fourier basis -/

/-- Frequency associated to Fourier index n:
- n = 0: frequency 0 (constant)
- n = 2k-1 (odd, k ≥ 1): frequency k (cosine)
- n = 2k (even, k ≥ 1): frequency k (sine) -/
def fourierFreq : ℕ → ℕ
  | 0 => 0
  | n + 1 => n / 2 + 1

/-- The real Fourier basis functions as bare functions `ℝ → ℝ`.
- Index 0: `1/√L` (constant)
- Index 2k-1: `√(2/L) · cos(2πkx/L)` (cosine)
- Index 2k: `√(2/L) · sin(2πkx/L)` (sine) -/
def fourierBasisFun : ℕ → ℝ → ℝ
  | 0 => fun _ => 1 / Real.sqrt L
  | n + 1 =>
    let k := (n / 2 + 1 : ℕ)
    if n % 2 = 0 then
      fun x => Real.sqrt (2 / L) * Real.cos (2 * Real.pi * k * x / L)
    else
      fun x => Real.sqrt (2 / L) * Real.sin (2 * Real.pi * k * x / L)

/-- Each Fourier basis function is smooth. -/
theorem fourierBasisFun_smooth (n : ℕ) : ContDiff ℝ ⊤ (fourierBasisFun (L := L) n) := by
  cases n with
  | zero => exact contDiff_const
  | succ m =>
    simp only [fourierBasisFun]
    split
    · -- cos case: x ↦ C * cos(a*x/L) is smooth (composition of smooth functions)
      exact contDiff_const.mul (Real.contDiff_cos.comp
        ((contDiff_const.mul contDiff_id).div contDiff_const (fun _ => ne_of_gt hL.out)))
    · -- sin case
      exact contDiff_const.mul (Real.contDiff_sin.comp
        ((contDiff_const.mul contDiff_id).div contDiff_const (fun _ => ne_of_gt hL.out)))

/-- Each Fourier basis function is L-periodic. -/
theorem fourierBasisFun_periodic (n : ℕ) :
    Function.Periodic (fourierBasisFun (L := L) n) L := by
  intro x
  cases n with
  | zero => simp [fourierBasisFun]
  | succ m =>
    simp only [fourierBasisFun]
    set k := (m / 2 + 1 : ℕ)
    have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL.out
    have h_arg : 2 * Real.pi * ↑k * (x + L) / L =
        2 * Real.pi * ↑k * x / L + ↑k * (2 * Real.pi) := by
      field_simp
    split
    · -- cosine: cos(2πk(x+L)/L) = cos(2πkx/L + 2πk) = cos(2πkx/L)
      show Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑k * (x + L) / L) =
        Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑k * x / L)
      rw [h_arg, Real.cos_add_nat_mul_two_pi]
    · -- sine: sin(2πk(x+L)/L) = sin(2πkx/L + 2πk) = sin(2πkx/L)
      show Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑k * (x + L) / L) =
        Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑k * x / L)
      rw [h_arg, Real.sin_add_nat_mul_two_pi]

/-- The real Fourier basis as elements of `SmoothCircle L`. -/
def fourierBasis (n : ℕ) : SmoothCircle L :=
  ⟨fourierBasisFun n, fourierBasisFun_periodic n, fourierBasisFun_smooth n⟩

@[simp] theorem fourierBasis_apply (n : ℕ) (x : ℝ) :
    (fourierBasis (L := L) n : ℝ → ℝ) x = fourierBasisFun (L := L) n x := rfl

/-! ### Fourier coefficients -/

open MeasureTheory in
/-- The n-th real Fourier coefficient of f, defined as the inner product
`(1/L) ∫₀ᴸ f(x) · ψ_n(x) dx`. -/
def fourierCoeffReal (n : ℕ) (f : SmoothCircle L) : ℝ :=
  (1 / L) * ∫ x in Set.Icc 0 L, f x * fourierBasisFun (L := L) n x

/-- The Fourier coefficient is linear. -/
theorem fourierCoeffReal_add (n : ℕ) (f g : SmoothCircle L) :
    fourierCoeffReal n (f + g) = fourierCoeffReal n f + fourierCoeffReal n g := by
  unfold fourierCoeffReal
  rw [← mul_add]; congr 1
  have h1 : ∀ x, (f + g) x * fourierBasisFun (L := L) n x =
    f x * fourierBasisFun (L := L) n x + g x * fourierBasisFun (L := L) n x :=
    fun x => by simp [add_apply, add_mul]
  simp_rw [h1]
  exact MeasureTheory.integral_add
    (f.continuous.mul (fourierBasisFun_smooth n).continuous |>.continuousOn.integrableOn_Icc)
    (g.continuous.mul (fourierBasisFun_smooth n).continuous |>.continuousOn.integrableOn_Icc)

/-- The Fourier coefficient is homogeneous. -/
theorem fourierCoeffReal_smul (n : ℕ) (r : ℝ) (f : SmoothCircle L) :
    fourierCoeffReal n (r • f) = r * fourierCoeffReal n f := by
  unfold fourierCoeffReal
  have h1 : ∀ x, (r • f) x * fourierBasisFun (L := L) n x =
    r * (f x * fourierBasisFun (L := L) n x) :=
    fun x => by simp [smul_apply, mul_assoc]
  simp_rw [h1, MeasureTheory.integral_const_mul]
  ring

/-- The Fourier coefficient as a linear map. -/
def fourierCoeffLM (n : ℕ) : SmoothCircle L →ₗ[ℝ] ℝ where
  toFun := fourierCoeffReal n
  map_add' := fourierCoeffReal_add n
  map_smul' r f := by simp [fourierCoeffReal_smul, smul_eq_mul]

/-- The Fourier coefficient as a continuous linear map.

Continuity follows from `|c_n(f)| ≤ (1/L) · L · sup|ψ_n| · sup|f| ≤ C · p_0(f)`. -/
def fourierCoeffCLM (n : ℕ) : SmoothCircle L →L[ℝ] ℝ where
  toLinearMap := fourierCoeffLM n
  cont := by
    apply Seminorm.continuous_from_bounded smoothCircle_withSeminorms (norm_withSeminorms ℝ ℝ)
    intro _
    -- |c_n(f)| = |(1/L) ∫₀ᴸ f·ψ_n dx| ≤ sup|ψ_n| · p_0(f)
    sorry

/-! ### Orthogonality -/

/-- Orthogonality of the real Fourier basis:
`(1/L) ∫₀ᴸ ψ_i(x) ψ_j(x) dx = δ_{ij}`. -/
theorem fourierCoeffReal_fourierBasis (i j : ℕ) :
    fourierCoeffReal (L := L) i (fourierBasis j) = if i = j then 1 else 0 := by
  sorry

/-! ### Sobolev seminorm of Fourier basis: polynomial growth -/

/-- The k-th Sobolev seminorm of the n-th Fourier basis element grows polynomially:
`p_k(ψ_n) ≤ C · (1 + n)^k`. -/
theorem sobolevSeminorm_fourierBasis_le (k : ℕ) :
    ∃ C > 0, ∀ n : ℕ, sobolevSeminorm (L := L) k (fourierBasis n) ≤
      C * (1 + (n : ℝ)) ^ k := by
  sorry

end SmoothCircle

end GaussianField
