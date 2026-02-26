/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Smooth Periodic Functions on the Circle

Defines `SmoothMap_Circle L ℝ`, the space of L-periodic smooth functions `ℝ → ℝ`,
equipped with Sobolev sup-seminorms and a real Fourier basis.

## Main definitions

- `SmoothMap_Circle L ℝ` — L-periodic smooth functions
- `SmoothMap_Circle.sobolevSeminorm k` — the k-th Sobolev sup-norm: `sup_{x ∈ [0,L]} |f^(k)(x)|`
- `SmoothMap_Circle.fourierBasis n` — orthonormal real Fourier basis indexed by ℕ
- `SmoothMap_Circle.fourierCoeffReal n` — real Fourier coefficient functionals

## Mathematical background

The space C∞(S¹) of smooth L-periodic functions is a nuclear Fréchet space
with topology given by the family of Sobolev sup-norms
`p_k(f) = sup_{x ∈ [0,L]} |f^(k)(x)|`. The real Fourier basis
`{1/√L, √(2/L)·cos(2πnx/L), √(2/L)·sin(2πnx/L)}` provides a Schauder
basis with polynomial growth and rapid coefficient decay.
-/

import Nuclear.NuclearTensorProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section

namespace GaussianField

/-! ## SmoothMap_Circle type definition -/

/-- An L-periodic smooth function `ℝ → ℝ`. Elements represent smooth functions
on the circle `ℝ/Lℤ`, stored as periodic functions on `ℝ` for calculus convenience. -/
structure SmoothMap_Circle (L : ℝ) (F : Type*) [Fact (0 < L)] where
  toFun : ℝ → ℝ
  periodic' : Function.Periodic toFun L
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun

variable {L : ℝ} [hL : Fact (0 < L)]

namespace SmoothMap_Circle

/-! ### Function-like structure -/

instance instFunLike : FunLike (SmoothMap_Circle L ℝ) ℝ ℝ where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

@[ext]
theorem ext {f g : SmoothMap_Circle L ℝ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp] theorem coe_mk (f : ℝ → ℝ) (hp : Function.Periodic f L)
    (hs : ContDiff ℝ (⊤ : ℕ∞) f) :
    ((⟨f, hp, hs⟩ : SmoothMap_Circle L ℝ) : ℝ → ℝ) = f := rfl

theorem periodic (f : SmoothMap_Circle L ℝ) : Function.Periodic f L := f.periodic'

theorem smooth (f : SmoothMap_Circle L ℝ) : ContDiff ℝ (⊤ : ℕ∞) f := f.smooth'

theorem continuous (f : SmoothMap_Circle L ℝ) : Continuous f := f.smooth.continuous

theorem contDiffAt_of_smooth (f : SmoothMap_Circle L ℝ) (k : ℕ) (x : ℝ) :
    ContDiffAt ℝ (↑k) f x :=
  (f.smooth.of_le (by exact_mod_cast le_top)).contDiffAt

/-! ### Algebraic structure -/

instance instZero : Zero (SmoothMap_Circle L ℝ) :=
  ⟨⟨0, fun _ => rfl, contDiff_const⟩⟩

@[simp] theorem coe_zero : (↑(0 : SmoothMap_Circle L ℝ) : ℝ → ℝ) = 0 := rfl
@[simp] theorem zero_apply (x : ℝ) : (0 : SmoothMap_Circle L ℝ) x = 0 := rfl

private theorem periodic_add (f g : SmoothMap_Circle L ℝ) :
    Function.Periodic (f + g : ℝ → ℝ) L :=
  fun x => show f (x + L) + g (x + L) = f x + g x by
    rw [f.periodic x, g.periodic x]

instance instAdd : Add (SmoothMap_Circle L ℝ) :=
  ⟨fun f g => ⟨f + g, periodic_add f g, f.smooth.add g.smooth⟩⟩

@[simp] theorem add_apply (f g : SmoothMap_Circle L ℝ) (x : ℝ) : (f + g) x = f x + g x := rfl

private theorem periodic_neg (f : SmoothMap_Circle L ℝ) :
    Function.Periodic (fun x => -f x) L :=
  fun x => show -f (x + L) = -f x by rw [f.periodic x]

instance instNeg : Neg (SmoothMap_Circle L ℝ) :=
  ⟨fun f => ⟨fun x => -f x, periodic_neg f, f.smooth.neg⟩⟩

@[simp] theorem neg_apply (f : SmoothMap_Circle L ℝ) (x : ℝ) : (-f) x = -f x := rfl

private theorem periodic_sub (f g : SmoothMap_Circle L ℝ) :
    Function.Periodic (fun x => f x - g x) L :=
  fun x => show f (x + L) - g (x + L) = f x - g x by
    rw [f.periodic x, g.periodic x]

instance instSub : Sub (SmoothMap_Circle L ℝ) :=
  ⟨fun f g => ⟨fun x => f x - g x, periodic_sub f g, f.smooth.sub g.smooth⟩⟩

private theorem periodic_smul (r : ℝ) (f : SmoothMap_Circle L ℝ) :
    Function.Periodic (fun x => r * f x) L :=
  fun x => show r * f (x + L) = r * f x by rw [f.periodic x]

instance instSMul : SMul ℝ (SmoothMap_Circle L ℝ) :=
  ⟨fun r f => ⟨fun x => r * f x, periodic_smul r f, f.smooth.const_smul r⟩⟩

@[simp] theorem smul_apply (r : ℝ) (f : SmoothMap_Circle L ℝ) (x : ℝ) :
    (r • f) x = r * f x := rfl

instance instAddCommGroup : AddCommGroup (SmoothMap_Circle L ℝ) where
  add_assoc f g h := ext fun x => add_assoc _ _ _
  zero_add f := ext fun x => zero_add _
  add_zero f := ext fun x => add_zero _
  neg_add_cancel f := ext fun x => neg_add_cancel _
  add_comm f g := ext fun x => add_comm _ _
  nsmul := nsmulRec
  zsmul := zsmulRec

instance instModule : Module ℝ (SmoothMap_Circle L ℝ) where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-! ### Iterated derivatives of smooth periodic functions -/

/-- The k-th derivative of a smooth periodic function is continuous. -/
theorem continuous_iteratedDeriv (f : SmoothMap_Circle L ℝ) (k : ℕ) :
    Continuous (iteratedDeriv k f) :=
  f.smooth.continuous_iteratedDeriv k (by exact_mod_cast le_top)

/-- The k-th derivative of a smooth periodic function is periodic.
Proof: by induction on k, using that the derivative of a periodic
differentiable function is periodic. -/
theorem periodic_iteratedDeriv (f : SmoothMap_Circle L ℝ) (k : ℕ) :
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
      fun y => (f.smooth.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top n)).differentiableAt
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
theorem bddAbove_norm_iteratedDeriv_image (f : SmoothMap_Circle L ℝ) (k : ℕ) :
    BddAbove ((fun x => ‖iteratedDeriv k f x‖) '' Set.Icc 0 L) :=
  (isCompact_Icc.image (f.continuous_iteratedDeriv k).norm).bddAbove

/-- [0, L] is nonempty when L > 0. -/
theorem Icc_nonempty : (Set.Icc (0 : ℝ) L).Nonempty :=
  Set.nonempty_Icc.mpr (le_of_lt hL.out)

/-! ### Sobolev sup-seminorms -/

/-- The Sobolev sup-seminorm: `p_k(f) = sup_{x ∈ [0,L]} ‖f^(k)(x)‖`. -/
def sobolevSeminorm (k : ℕ) : Seminorm ℝ (SmoothMap_Circle L ℝ) where
  toFun f := sSup ((fun x => ‖iteratedDeriv k f x‖) '' Set.Icc 0 L)
  map_zero' := by
    apply le_antisymm
    · apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
      rintro _ ⟨x, _, rfl⟩
      simp
    · exact le_csSup_of_le
        ((0 : SmoothMap_Circle L ℝ).bddAbove_norm_iteratedDeriv_image k)
        ⟨0, Set.left_mem_Icc.mpr (le_of_lt hL.out), rfl⟩
        (by simp)
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
    -- (-f : SmoothMap_Circle L ℝ) coerces to -(↑f : ℝ → ℝ) definitionally.
    -- iteratedDeriv_neg then gives iteratedDeriv k (-↑f) x = -(iteratedDeriv k ↑f x),
    -- and norm_neg gives ‖-(iteratedDeriv k ↑f x)‖ = ‖iteratedDeriv k ↑f x‖.
    have hcoe : ((-f : SmoothMap_Circle L ℝ) : ℝ → ℝ) = -(↑f : ℝ → ℝ) := rfl
    simp_rw [hcoe, iteratedDeriv_neg, norm_neg]
  smul' r f := by
    -- (r • f : SmoothMap_Circle L ℝ) coerces to r • (↑f : ℝ → ℝ) (pointwise scalar multiplication).
    -- iteratedDeriv_const_smul_field gives iteratedDeriv k (r • ↑f) x = r • iteratedDeriv k ↑f x,
    -- and norm_smul gives ‖r • iteratedDeriv k ↑f x‖ = ‖r‖ * ‖iteratedDeriv k ↑f x‖.
    -- Finally, sSup of {‖r‖ * y | y ∈ S} = ‖r‖ * sSup S by Real.sSup_smul_of_nonneg.
    have hcoe : ((r • f : SmoothMap_Circle L ℝ) : ℝ → ℝ) = r • (↑f : ℝ → ℝ) := by
      ext x; simp [smul_apply]
    simp_rw [hcoe, iteratedDeriv_const_smul_field, norm_smul]
    open Pointwise in
    rw [show (fun x => ‖r‖ * ‖iteratedDeriv k (↑f : ℝ → ℝ) x‖) '' Set.Icc 0 L =
         ‖r‖ • ((fun x => ‖iteratedDeriv k (↑f : ℝ → ℝ) x‖) '' Set.Icc 0 L) from ?_]
    · rw [Real.sSup_smul_of_nonneg (norm_nonneg r), smul_eq_mul]
    · ext x; simp [Set.mem_image, Set.mem_smul_set, smul_eq_mul]

/-- The Sobolev seminorm is nonneg. -/
theorem sobolevSeminorm_nonneg (k : ℕ) (f : SmoothMap_Circle L ℝ) :
    0 ≤ sobolevSeminorm k f :=
  le_csSup_of_le (f.bddAbove_norm_iteratedDeriv_image k)
    ⟨0, Set.left_mem_Icc.mpr (le_of_lt hL.out), rfl⟩
    (norm_nonneg _)

/-- Pointwise bound: `‖f^(k)(x)‖ ≤ p_k(f)` for `x ∈ [0, L]`. -/
theorem norm_iteratedDeriv_le_sobolevSeminorm (f : SmoothMap_Circle L ℝ) (k : ℕ)
    {x : ℝ} (hx : x ∈ Set.Icc 0 L) :
    ‖iteratedDeriv k f x‖ ≤ sobolevSeminorm k f :=
  le_csSup (f.bddAbove_norm_iteratedDeriv_image k) ⟨x, hx, rfl⟩

/-- Pointwise bound for any x (by periodicity). -/
theorem norm_iteratedDeriv_le_sobolevSeminorm' (f : SmoothMap_Circle L ℝ) (k : ℕ) (x : ℝ) :
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

instance instTopologicalSpace : TopologicalSpace (SmoothMap_Circle L ℝ) :=
  (SeminormFamily.moduleFilterBasis
    (𝕜 := ℝ) (sobolevSeminorm (L := L))).topology

theorem smoothCircle_withSeminorms :
    WithSeminorms (sobolevSeminorm : ℕ → Seminorm ℝ (SmoothMap_Circle L ℝ)) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (SmoothMap_Circle L ℝ) :=
  smoothCircle_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ (SmoothMap_Circle L ℝ) :=
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
theorem fourierBasisFun_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fourierBasisFun (L := L) n) := by
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

/-- The real Fourier basis as elements of `SmoothMap_Circle L ℝ`. -/
def fourierBasis (n : ℕ) : SmoothMap_Circle L ℝ :=
  ⟨fourierBasisFun n, fourierBasisFun_periodic n, fourierBasisFun_smooth n⟩

@[simp] theorem fourierBasis_apply (n : ℕ) (x : ℝ) :
    (fourierBasis (L := L) n : ℝ → ℝ) x = fourierBasisFun (L := L) n x := rfl

omit [Fact (0 < L)] in
/-- Each Fourier basis function is pointwise bounded. -/
theorem fourierBasisFun_abs_le (n : ℕ) (x : ℝ) :
    |fourierBasisFun (L := L) n x| ≤ max (1 / Real.sqrt L) (Real.sqrt (2 / L)) := by
  cases n with
  | zero =>
    simp only [fourierBasisFun]
    rw [abs_of_nonneg (by positivity)]
    exact le_max_left _ _
  | succ m =>
    simp only [fourierBasisFun]
    split
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (2 / L) * |Real.cos _|
          ≤ Real.sqrt (2 / L) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / L) := mul_one _
        _ ≤ max _ _ := le_max_right _ _
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (2 / L) * |Real.sin _|
          ≤ Real.sqrt (2 / L) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / L) := mul_one _
        _ ≤ max _ _ := le_max_right _ _

/-! ### Fourier coefficients -/

open MeasureTheory in
/-- The n-th real Fourier coefficient of f, defined as the L² inner product
`∫₀ᴸ f(x) · ψ_n(x) dx` where `{ψ_n}` is the L²-orthonormal basis. -/
def fourierCoeffReal (n : ℕ) (f : SmoothMap_Circle L ℝ) : ℝ :=
  ∫ x in Set.Icc 0 L, f x * fourierBasisFun (L := L) n x

/-- The Fourier coefficient is linear. -/
theorem fourierCoeffReal_add (n : ℕ) (f g : SmoothMap_Circle L ℝ) :
    fourierCoeffReal n (f + g) = fourierCoeffReal n f + fourierCoeffReal n g := by
  unfold fourierCoeffReal
  have h1 : ∀ x, (f + g) x * fourierBasisFun (L := L) n x =
    f x * fourierBasisFun (L := L) n x + g x * fourierBasisFun (L := L) n x :=
    fun x => by simp [add_apply, add_mul]
  simp_rw [h1]
  exact MeasureTheory.integral_add
    (f.continuous.mul (fourierBasisFun_smooth n).continuous |>.continuousOn.integrableOn_Icc)
    (g.continuous.mul (fourierBasisFun_smooth n).continuous |>.continuousOn.integrableOn_Icc)

/-- The Fourier coefficient is homogeneous. -/
theorem fourierCoeffReal_smul (n : ℕ) (r : ℝ) (f : SmoothMap_Circle L ℝ) :
    fourierCoeffReal n (r • f) = r * fourierCoeffReal n f := by
  unfold fourierCoeffReal
  have h1 : ∀ x, (r • f) x * fourierBasisFun (L := L) n x =
    r * (f x * fourierBasisFun (L := L) n x) :=
    fun x => by simp [smul_apply, mul_assoc]
  simp_rw [h1, MeasureTheory.integral_const_mul]

/-- The Fourier coefficient as a linear map. -/
def fourierCoeffLM (n : ℕ) : SmoothMap_Circle L ℝ →ₗ[ℝ] ℝ where
  toFun := fourierCoeffReal n
  map_add' := fourierCoeffReal_add n
  map_smul' r f := by simp [fourierCoeffReal_smul, smul_eq_mul]

/-! ### Integral bound for Fourier coefficients -/

open MeasureTheory in
/-- Pointwise bound: `|c_n(f)| ≤ C · p_0(f)` where C = L · max(1/√L, √(2/L)).
Uses `norm_setIntegral_le_of_norm_le_const` and `fourierBasisFun_abs_le`. -/
theorem fourierCoeffReal_bound (n : ℕ) (f : SmoothMap_Circle L ℝ) :
    ‖fourierCoeffReal (L := L) n f‖ ≤
      (max (1 / Real.sqrt L) (Real.sqrt (2 / L)) * L) * sobolevSeminorm 0 f := by
  unfold fourierCoeffReal
  rw [Real.norm_eq_abs]
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  have hM_nonneg : 0 ≤ M := le_max_of_le_right (Real.sqrt_nonneg _)
  have h_bound : ∀ x ∈ Set.Icc (0 : ℝ) L,
      ‖f x * fourierBasisFun (L := L) n x‖ ≤ sobolevSeminorm 0 f * M := by
    intro x hx
    rw [norm_mul]
    apply mul_le_mul _ _ (norm_nonneg _) (sobolevSeminorm_nonneg 0 f)
    · have := norm_iteratedDeriv_le_sobolevSeminorm f 0 hx
      rwa [iteratedDeriv_zero] at this
    · rw [Real.norm_eq_abs]; exact fourierBasisFun_abs_le n x
  calc |∫ x in Set.Icc 0 L, f x * fourierBasisFun n x|
      ≤ (sobolevSeminorm 0 f * M) * volume.real (Set.Icc (0 : ℝ) L) :=
        norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top h_bound
    _ = M * L * sobolevSeminorm 0 f := by
        rw [Real.volume_real_Icc_of_le (le_of_lt hL.out)]; ring

/-- The Fourier coefficient as a continuous linear map.

Continuity follows from `|c_n(f)| ≤ C · p_0(f)`. -/
def fourierCoeffCLM (n : ℕ) : SmoothMap_Circle L ℝ →L[ℝ] ℝ where
  toLinearMap := fourierCoeffLM n
  cont := by
    apply Seminorm.continuous_from_bounded smoothCircle_withSeminorms (norm_withSeminorms ℝ ℝ)
    intro _
    set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
    refine ⟨{0}, ⟨M * L, mul_nonneg (le_max_of_le_right (Real.sqrt_nonneg _))
      (le_of_lt hL.out)⟩, fun f => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, NNReal.smul_def, Seminorm.smul_apply,
      coe_normSeminorm, NNReal.coe_mk]
    exact fourierCoeffReal_bound n f

/-! ### Orthogonality -/

-- Convert set integral on Icc to interval integral
private theorem setIntegral_Icc_eq_intervalIntegral (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (_hf : IntervalIntegrable f MeasureTheory.volume a b) :
    ∫ x in Set.Icc a b, f x = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

-- Integral of cos(2πkx/L) over [0, L] is 0 for k ≥ 1
private theorem sin_two_pi_mul_nat (k : ℕ) : Real.sin (2 * Real.pi * k) = 0 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Real.sin_nat_mul_two_pi_sub (x := (0 : ℝ)) k)

private theorem cos_two_pi_mul_nat (k : ℕ) : Real.cos (2 * Real.pi * k) = 1 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (Real.cos_nat_mul_two_pi k)

private theorem integral_cos_period (k : ℕ) (hk : 0 < k) :
    ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * k * x / L) = 0 := by
  set c := 2 * Real.pi * k / L
  have hc : c ≠ 0 := by simp only [c]; exact div_ne_zero (by positivity) (ne_of_gt hL.out)
  have h_rw : ∀ x : ℝ, 2 * Real.pi * ↑k * x / L = c * x := fun x => by
    simp only [c]; ring
  simp_rw [h_rw]
  rw [intervalIntegral.integral_comp_mul_left _ hc, mul_zero]
  have hcL : c * L = 2 * Real.pi * k := by
    simp only [c]; field_simp; exact div_self (ne_of_gt hL.out)
  rw [hcL, integral_cos, sin_two_pi_mul_nat, Real.sin_zero, sub_self,
    smul_zero]

-- Integral of sin(2πkx/L) over [0, L] is 0 for k ≥ 1
private theorem integral_sin_period (k : ℕ) (hk : 0 < k) :
    ∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * k * x / L) = 0 := by
  set c := 2 * Real.pi * k / L
  have hc : c ≠ 0 := by simp only [c]; exact div_ne_zero (by positivity) (ne_of_gt hL.out)
  have h_rw : ∀ x : ℝ, 2 * Real.pi * ↑k * x / L = c * x := fun x => by
    simp only [c]; ring
  simp_rw [h_rw]
  rw [intervalIntegral.integral_comp_mul_left _ hc, mul_zero]
  have hcL : c * L = 2 * Real.pi * k := by
    simp only [c]; field_simp; exact div_self (ne_of_gt hL.out)
  rw [hcL, integral_sin, cos_two_pi_mul_nat, Real.cos_zero, sub_self,
    smul_zero]

-- Helper: integral of cos/sin over [0, L] with integer frequency is 0
-- For general integer n ≠ 0, ∫₀ᴸ cos(2πnx/L) = 0 and ∫₀ᴸ sin(2πnx/L) = 0
private theorem integral_period_change_var_int (n : ℤ) (hn : n ≠ 0) (f : ℝ → ℝ) :
    ∫ x in (0 : ℝ)..L, f (2 * Real.pi * n * x / L) =
      (2 * Real.pi * n / L)⁻¹ * ∫ x in (0 : ℝ)..(2 * Real.pi * n), f x := by
  set c := 2 * Real.pi * n / L
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, div_eq_zero_iff]; push_neg
    exact ⟨mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)) (Int.cast_ne_zero.mpr hn),
      ne_of_gt hL.out⟩
  have h_rw : ∀ x : ℝ, 2 * Real.pi * ↑n * x / L = c * x := fun x => by
    simp only [c]; ring
  simp_rw [h_rw]
  have hcL : c * L = 2 * Real.pi * n := by
    simp only [c]; field_simp; exact div_self (ne_of_gt hL.out)
  rw [intervalIntegral.integral_comp_mul_left _ hc, mul_zero, hcL]
  simp [smul_eq_mul]

private theorem integral_cos_int_period (n : ℤ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * n * x / L) = 0 := by
  rw [integral_period_change_var_int (L := L) n hn Real.cos, integral_cos]
  -- sin(2πn) = 0 for integer n
  have h1 : Real.sin (2 * Real.pi * ↑n) = 0 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.sin_int_mul_two_pi_sub (x := (0 : ℝ)) n)
  rw [h1, Real.sin_zero, sub_self, mul_zero]

private theorem integral_sin_int_period (n : ℤ) (hn : n ≠ 0) :
    ∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * n * x / L) = 0 := by
  rw [integral_period_change_var_int (L := L) n hn Real.sin, integral_sin]
  -- cos(2πn) = 1 for integer n, so cos(0) - cos(2πn) = 1 - 1 = 0
  have h1 : Real.cos (2 * Real.pi * ↑n) = 1 := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Real.cos_int_mul_two_pi n)
  rw [Real.cos_zero, h1, sub_self, mul_zero]

-- Integral of cos(2πkx/L)·cos(2πℓx/L) over [0, L]
private theorem integral_cos_cos (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * k * x / L) *
      Real.cos (2 * Real.pi * ℓ * x / L) = if k = ℓ then L / 2 else 0 := by
  -- Product-to-sum: cos A · cos B = (cos(A-B) + cos(A+B))/2
  have h_prod : ∀ x : ℝ,
      Real.cos (2 * Real.pi * k * x / L) * Real.cos (2 * Real.pi * ℓ * x / L) =
      (Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L) +
       Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) / 2 := by
    intro x
    rw [show 2 * Real.pi * (↑k - ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L - 2 * Real.pi * ↑ℓ * x / L from by ring,
      show 2 * Real.pi * (↑k + ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L + 2 * Real.pi * ↑ℓ * x / L from by ring,
      Real.cos_sub, Real.cos_add]; ring
  simp_rw [h_prod, intervalIntegral.integral_div]
  -- ∫ cos(2π(k+ℓ)x/L) = 0 (always, since k+ℓ ≥ 2)
  have h_sum : ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L) = 0 := by
    rw [show (2 : ℝ) * Real.pi * (↑k + ↑ℓ) = 2 * Real.pi * ↑(k + ℓ : ℤ) from by push_cast; ring]
    exact integral_cos_int_period (k + ℓ : ℤ) (by omega)
  -- Split integral of sum: ∫ (f + g) = (∫ f) + (∫ g)
  have h_split : (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L) +
      Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) =
      (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L)) +
      (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) := by
    apply intervalIntegral.integral_add
    all_goals exact (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [h_split, h_sum, add_zero]
  split_ifs with h
  · -- k = ℓ: ∫ cos(2π·0·x/L) = ∫ cos(0) = ∫ 1 = L
    subst h
    simp only [sub_self, mul_zero, zero_mul, zero_div, Real.cos_zero]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  · -- k ≠ ℓ: k - ℓ ≠ 0 as integers
    rw [show (2 : ℝ) * Real.pi * (↑k - ↑ℓ) = 2 * Real.pi * ↑(k - ℓ : ℤ) from by push_cast; ring]
    rw [integral_cos_int_period (k - ℓ : ℤ) (by omega), zero_div]

-- Integral of sin(2πkx/L)·sin(2πℓx/L) over [0, L]
private theorem integral_sin_sin (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    ∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * k * x / L) *
      Real.sin (2 * Real.pi * ℓ * x / L) = if k = ℓ then L / 2 else 0 := by
  -- Product-to-sum: sin A · sin B = (cos(A-B) - cos(A+B))/2
  have h_prod : ∀ x : ℝ,
      Real.sin (2 * Real.pi * k * x / L) * Real.sin (2 * Real.pi * ℓ * x / L) =
      (Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L) -
       Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) / 2 := by
    intro x
    rw [show 2 * Real.pi * (↑k - ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L - 2 * Real.pi * ↑ℓ * x / L from by ring,
      show 2 * Real.pi * (↑k + ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L + 2 * Real.pi * ↑ℓ * x / L from by ring,
      Real.cos_sub, Real.cos_add]; ring
  simp_rw [h_prod, intervalIntegral.integral_div]
  have h_sum : ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L) = 0 := by
    rw [show (2 : ℝ) * Real.pi * (↑k + ↑ℓ) = 2 * Real.pi * ↑(k + ℓ : ℤ) from by push_cast; ring]
    exact integral_cos_int_period (k + ℓ : ℤ) (by omega)
  have h_split : (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L) -
      Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) =
      (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k - ↑ℓ) * x / L)) -
      (∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * (↑k + ↑ℓ) * x / L)) := by
    apply intervalIntegral.integral_sub
    all_goals exact (Real.continuous_cos.comp (by fun_prop)).intervalIntegrable _ _
  rw [h_split, h_sum, sub_zero]
  split_ifs with h
  · subst h
    simp only [sub_self, mul_zero, zero_mul, zero_div, Real.cos_zero]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]
  · rw [show (2 : ℝ) * Real.pi * (↑k - ↑ℓ) = 2 * Real.pi * ↑(k - ℓ : ℤ) from by push_cast; ring]
    rw [integral_cos_int_period (k - ℓ : ℤ) (by omega), zero_div]

-- Integral of cos(2πkx/L)·sin(2πℓx/L) over [0, L] is 0
private theorem integral_cos_sin (k ℓ : ℕ) (hk : 0 < k) (hℓ : 0 < ℓ) :
    ∫ x in (0 : ℝ)..L, Real.cos (2 * Real.pi * k * x / L) *
      Real.sin (2 * Real.pi * ℓ * x / L) = 0 := by
  -- Product-to-sum: cos A · sin B = (sin(A+B) - sin(A-B))/2
  have h_prod : ∀ x : ℝ,
      Real.cos (2 * Real.pi * k * x / L) * Real.sin (2 * Real.pi * ℓ * x / L) =
      (Real.sin (2 * Real.pi * (↑k + ↑ℓ) * x / L) -
       Real.sin (2 * Real.pi * (↑k - ↑ℓ) * x / L)) / 2 := by
    intro x
    rw [show 2 * Real.pi * (↑k + ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L + 2 * Real.pi * ↑ℓ * x / L from by ring,
      show 2 * Real.pi * (↑k - ↑ℓ) * x / L =
        2 * Real.pi * ↑k * x / L - 2 * Real.pi * ↑ℓ * x / L from by ring,
      Real.sin_add, Real.sin_sub]; ring
  simp_rw [h_prod, intervalIntegral.integral_div]
  have h_sum : ∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * (↑k + ↑ℓ) * x / L) = 0 := by
    rw [show (2 : ℝ) * Real.pi * (↑k + ↑ℓ) = 2 * Real.pi * ↑(k + ℓ : ℤ) from by push_cast; ring]
    exact integral_sin_int_period (k + ℓ : ℤ) (by omega)
  have h_split : (∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * (↑k + ↑ℓ) * x / L) -
      Real.sin (2 * Real.pi * (↑k - ↑ℓ) * x / L)) =
      (∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * (↑k + ↑ℓ) * x / L)) -
      (∫ x in (0 : ℝ)..L, Real.sin (2 * Real.pi * (↑k - ↑ℓ) * x / L)) := by
    apply intervalIntegral.integral_sub
    all_goals exact (Real.continuous_sin.comp (by fun_prop)).intervalIntegrable _ _
  rw [h_split, h_sum, zero_sub]
  by_cases h : (k : ℤ) - ℓ = 0
  · have hk_eq : (↑k : ℝ) - ↑ℓ = 0 := by exact_mod_cast h
    simp only [hk_eq, mul_zero, zero_mul, zero_div, Real.sin_zero]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_zero, neg_zero, zero_div]
  · rw [show (2 : ℝ) * Real.pi * (↑k - ↑ℓ) = 2 * Real.pi * ↑(k - ℓ : ℤ) from by push_cast; ring]
    rw [integral_sin_int_period (k - ℓ : ℤ) h, neg_zero, zero_div]

/-- Orthogonality of the real Fourier basis:
`∫₀ᴸ ψ_i(x) ψ_j(x) dx = δ_{ij}`. -/
theorem fourierCoeffReal_fourierBasis (i j : ℕ) :
    fourierCoeffReal (L := L) i (fourierBasis j) = if i = j then 1 else 0 := by
  unfold fourierCoeffReal
  simp only [fourierBasis_apply]
  -- Convert set integral on Icc to interval integral
  have h_conv : ∫ x in Set.Icc 0 L, fourierBasisFun (L := L) j x * fourierBasisFun (L := L) i x =
      ∫ x in (0 : ℝ)..L, fourierBasisFun (L := L) j x * fourierBasisFun (L := L) i x :=
    setIntegral_Icc_eq_intervalIntegral _ 0 L (le_of_lt hL.out)
      ((fourierBasisFun_smooth (L := L) j).continuous.mul
        (fourierBasisFun_smooth (L := L) i).continuous).continuousOn.intervalIntegrable
  rw [h_conv]; clear h_conv
  -- Helper: rewrite integrand using pointwise equality
  have integral_rw : ∀ (f g : ℝ → ℝ) (_ : ∀ x, f x = g x),
      ∫ x in (0 : ℝ)..L, f x = ∫ x in (0 : ℝ)..L, g x :=
    fun f g h => intervalIntegral.integral_congr (fun x _ => h x)
  -- Case split on i and j
  rcases j with _ | j <;> rcases i with _ | i
  · -- i = 0, j = 0
    simp only [fourierBasisFun, ↓reduceIte]
    rw [integral_rw _ (fun _ => 1 / L) (fun _ => by
      rw [div_mul_div_comm, one_mul, ← sq, Real.sq_sqrt (le_of_lt hL.out)])]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero,
      one_div, mul_inv_cancel₀ (ne_of_gt hL.out)]
  · -- i > 0, j = 0
    simp only [fourierBasisFun]
    split
    · -- i+1 is cos
      rw [integral_rw _ (fun x => (1 / Real.sqrt L * Real.sqrt (2 / L)) *
          Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L)) (fun x => by ring)]
      rw [intervalIntegral.integral_const_mul, integral_cos_period (i / 2 + 1) (by omega), mul_zero]
      simp
    · -- i+1 is sin
      rw [integral_rw _ (fun x => (1 / Real.sqrt L * Real.sqrt (2 / L)) *
          Real.sin (2 * Real.pi * ↑(i / 2 + 1) * x / L)) (fun x => by ring)]
      rw [intervalIntegral.integral_const_mul, integral_sin_period (i / 2 + 1) (by omega), mul_zero]
      simp
  · -- i = 0, j > 0
    simp only [fourierBasisFun]
    split
    · -- j+1 is cos
      rw [integral_rw _ (fun x => (Real.sqrt (2 / L) / Real.sqrt L) *
          Real.cos (2 * Real.pi * ↑(j / 2 + 1) * x / L)) (fun x => by ring)]
      rw [intervalIntegral.integral_const_mul, integral_cos_period (j / 2 + 1) (by omega), mul_zero]
      simp
    · -- j+1 is sin
      rw [integral_rw _ (fun x => (Real.sqrt (2 / L) / Real.sqrt L) *
          Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L)) (fun x => by ring)]
      rw [intervalIntegral.integral_const_mul, integral_sin_period (j / 2 + 1) (by omega), mul_zero]
      simp
  · -- both i, j > 0
    simp only [fourierBasisFun]
    -- Helper: √(2/L) * a * (√(2/L) * b) = (2/L) * (a * b)
    have factor : ∀ a b : ℝ, Real.sqrt (2 / L) * a * (Real.sqrt (2 / L) * b) = 2 / L * (a * b) := by
      intro a b
      have h : Real.sqrt (2 / L) * Real.sqrt (2 / L) = 2 / L :=
        Real.mul_self_sqrt (le_of_lt (div_pos two_pos hL.out))
      calc _ = Real.sqrt (2 / L) * Real.sqrt (2 / L) * (a * b) := by ring
        _ = 2 / L * (a * b) := by rw [h]
    -- Split on parity
    by_cases hi : i % 2 = 0 <;> by_cases hj : j % 2 = 0 <;> simp only [hi, hj, ↓reduceIte]
    · -- hj=0, hi=0: cos(j)*cos(i)
      have h_eq : ∫ x in (0 : ℝ)..L,
          Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          (Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L)) =
          2 / L * ∫ x in (0 : ℝ)..L,
          Real.cos (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun x _ => factor _ _)
      rw [h_eq, integral_cos_cos (j / 2 + 1) (i / 2 + 1) (by omega) (by omega)]
      by_cases heq : i + 1 = j + 1
      · have : j / 2 + 1 = i / 2 + 1 := by omega
        simp only [if_pos this, if_pos heq]; field_simp; exact div_self (ne_of_gt hL.out)
      · have : j / 2 + 1 ≠ i / 2 + 1 := by omega
        simp only [if_neg this, if_neg heq, mul_zero]
    · -- hj≠0, hi=0: sin(j)*cos(i)
      have hij : i + 1 ≠ j + 1 := by omega
      -- Integrand: √(2/L)*sin_j * (√(2/L)*cos_i) → factor then swap for integral_cos_sin
      have h_eq : ∫ x in (0 : ℝ)..L,
          Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          (Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L)) =
          2 / L * ∫ x in (0 : ℝ)..L,
          Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L) *
          Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr; intro x _
        have h1 := factor (Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L))
          (Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L))
        linarith [mul_comm (Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L))
          (Real.cos (2 * Real.pi * ↑(i / 2 + 1) * x / L))]
      rw [h_eq, integral_cos_sin (i / 2 + 1) (j / 2 + 1) (by omega) (by omega), mul_zero]
      simp only [if_neg hij]
    · -- hj=0, hi≠0: cos(j)*sin(i)
      have hij : i + 1 ≠ j + 1 := by omega
      have h_eq : ∫ x in (0 : ℝ)..L,
          Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          (Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑(i / 2 + 1) * x / L)) =
          2 / L * ∫ x in (0 : ℝ)..L,
          Real.cos (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          Real.sin (2 * Real.pi * ↑(i / 2 + 1) * x / L) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun x _ => factor _ _)
      rw [h_eq, integral_cos_sin (j / 2 + 1) (i / 2 + 1) (by omega) (by omega), mul_zero]
      simp only [if_neg hij]
    · -- hj≠0, hi≠0: sin(j)*sin(i)
      have h_eq : ∫ x in (0 : ℝ)..L,
          Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          (Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑(i / 2 + 1) * x / L)) =
          2 / L * ∫ x in (0 : ℝ)..L,
          Real.sin (2 * Real.pi * ↑(j / 2 + 1) * x / L) *
          Real.sin (2 * Real.pi * ↑(i / 2 + 1) * x / L) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun x _ => factor _ _)
      rw [h_eq, integral_sin_sin (j / 2 + 1) (i / 2 + 1) (by omega) (by omega)]
      by_cases heq : i + 1 = j + 1
      · have : j / 2 + 1 = i / 2 + 1 := by omega
        simp only [if_pos this, if_pos heq]; field_simp; exact div_self (ne_of_gt hL.out)
      · have : j / 2 + 1 ≠ i / 2 + 1 := by omega
        simp only [if_neg this, if_neg heq, mul_zero]

/-! ### Sobolev seminorm of Fourier basis: polynomial growth -/

/-- Pointwise derivative bound for `A * cos(c * x)`. -/
private theorem norm_iteratedDeriv_cos_mul (A c : ℝ) (k : ℕ) (x : ℝ) (hA : 0 ≤ A) :
    ‖iteratedDeriv k (fun x => A * Real.cos (c * x)) x‖ ≤ A * |c| ^ k := by
  rw [iteratedDeriv_const_mul_field,
      congr_fun (@iteratedDeriv_comp_const_mul ℝ _ k Real.cos
        (Real.contDiff_cos.of_le (by exact_mod_cast le_top)) c) x,
      norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hA,
      Real.norm_eq_abs, abs_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_cos_le_one k _)
      (pow_nonneg (abs_nonneg _) _)).trans (mul_one _).le) hA

/-- Pointwise derivative bound for `A * sin(c * x)`. -/
private theorem norm_iteratedDeriv_sin_mul (A c : ℝ) (k : ℕ) (x : ℝ) (hA : 0 ≤ A) :
    ‖iteratedDeriv k (fun x => A * Real.sin (c * x)) x‖ ≤ A * |c| ^ k := by
  rw [iteratedDeriv_const_mul_field,
      congr_fun (@iteratedDeriv_comp_const_mul ℝ _ k Real.sin
        (Real.contDiff_sin.of_le (by exact_mod_cast le_top)) c) x,
      norm_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hA,
      Real.norm_eq_abs, abs_pow, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    ((mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_sin_le_one k _)
      (pow_nonneg (abs_nonneg _) _)).trans (mul_one _).le) hA

/-- The k-th Sobolev seminorm of the n-th Fourier basis element grows polynomially:
`p_k(ψ_n) ≤ C · (1 + n)^k`. -/
theorem sobolevSeminorm_fourierBasis_le (k : ℕ) :
    ∃ C > 0, ∀ n : ℕ, sobolevSeminorm (L := L) k (fourierBasis n) ≤
      C * (1 + (n : ℝ)) ^ k := by
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  set ω := 2 * Real.pi / L
  refine ⟨max 1 (M * ω ^ k), by positivity, fun n => ?_⟩
  -- Bound the sup of ‖iteratedDeriv k (fourierBasisFun n) x‖ over [0, L]
  apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
  rintro _ ⟨x, _, rfl⟩
  cases n with
  | zero =>
    -- ψ_0 = 1/√L (constant): iteratedDeriv k = if k=0 then 1/√L else 0
    simp only [fourierBasis, coe_mk, fourierBasisFun, Nat.cast_zero, add_zero]
    rw [iteratedDeriv_const]
    split
    · -- k = 0: ‖1/√L‖ ≤ max 1 M * 1
      subst_vars; simp only [pow_zero, mul_one]
      calc ‖(1 : ℝ) / Real.sqrt L‖ = 1 / Real.sqrt L := by
            rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        _ ≤ M := le_max_left _ _
        _ ≤ max 1 M := le_max_right _ _
    · -- k ≥ 1: ‖0‖ = 0 ≤ anything
      simp
  | succ m =>
    simp only [fourierBasis, coe_mk]
    have hω_nonneg : 0 ≤ ω := div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hL.out.le
    set c := ω * ↑(m / 2 + 1) with hc_def
    have hM : 0 ≤ Real.sqrt (2 / L) := Real.sqrt_nonneg _
    have hc_nonneg : 0 ≤ c := mul_nonneg hω_nonneg (Nat.cast_nonneg _)
    have hc_bound : |c| ≤ ω * (1 + ↑(m + 1)) := by
      rw [abs_of_nonneg hc_nonneg]
      apply mul_le_mul_of_nonneg_left _ hω_nonneg
      have : m / 2 ≤ m := Nat.div_le_self m 2
      exact_mod_cast (by omega : m / 2 + 1 ≤ 1 + (m + 1))
    -- fourierBasisFun (m+1) is √(2/L) * cos(c*x) or √(2/L) * sin(c*x)
    by_cases hm : m % 2 = 0
    · -- cos case
      have hfun : fourierBasisFun (L := L) (m + 1) = fun x => Real.sqrt (2 / L) * Real.cos (c * x) := by
        ext y; simp only [fourierBasisFun, hm, ite_true]; congr 1; simp only [hc_def, ω]; ring_nf
      rw [hfun]
      calc ‖iteratedDeriv k (fun x => Real.sqrt (2 / L) * Real.cos (c * x)) x‖
          ≤ Real.sqrt (2 / L) * |c| ^ k := norm_iteratedDeriv_cos_mul _ c k x hM
        _ ≤ M * (ω * (1 + ↑(m + 1))) ^ k := by
            apply mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (abs_nonneg _) hc_bound _)
              (pow_nonneg (abs_nonneg _) _) (le_max_of_le_right hM)
        _ = M * ω ^ k * (1 + ↑(m + 1)) ^ k := by rw [mul_pow]; ring
        _ ≤ max 1 (M * ω ^ k) * (1 + ↑(m + 1)) ^ k :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by positivity) _)
    · -- sin case
      have hfun : fourierBasisFun (L := L) (m + 1) = fun x => Real.sqrt (2 / L) * Real.sin (c * x) := by
        ext y; simp only [fourierBasisFun, hm, ite_false]; congr 1; simp only [hc_def, ω]; ring_nf
      rw [hfun]
      calc ‖iteratedDeriv k (fun x => Real.sqrt (2 / L) * Real.sin (c * x)) x‖
          ≤ Real.sqrt (2 / L) * |c| ^ k := norm_iteratedDeriv_sin_mul _ c k x hM
        _ ≤ M * (ω * (1 + ↑(m + 1))) ^ k := by
            apply mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ (abs_nonneg _) hc_bound _)
              (pow_nonneg (abs_nonneg _) _) (le_max_of_le_right hM)
        _ = M * ω ^ k * (1 + ↑(m + 1)) ^ k := by rw [mul_pow]; ring
        _ ≤ max 1 (M * ω ^ k) * (1 + ↑(m + 1)) ^ k :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg (by positivity) _)

end SmoothMap_Circle

end GaussianField
