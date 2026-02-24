/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Complexification of real vector spaces

Given a real vector space E, its complexification E_ℂ = E ⊕ iE is the
complex vector space of formal sums f + ig with f, g ∈ E and the
complex scalar action (a + bi)(f + ig) = (af - bg) + i(ag + bf).

We represent this as a structure with `re` and `im` fields (rather than
`E × E`) to avoid typeclass diamonds with `Prod.instModule`.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

namespace GaussianField

/-- The complexification of a real vector space E.
Elements represent f + ig where f = re, g = im. -/
@[ext]
structure Complexification (E : Type*) where
  re : E
  im : E

namespace Complexification

variable {E : Type*} [AddCommGroup E]

/-! ## Additive group structure (componentwise) -/

instance : Zero (Complexification E) where zero := ⟨0, 0⟩
instance : Add (Complexification E) where add p q := ⟨p.re + q.re, p.im + q.im⟩
instance : Neg (Complexification E) where neg p := ⟨-p.re, -p.im⟩
instance : Sub (Complexification E) where sub p q := ⟨p.re - q.re, p.im - q.im⟩

@[simp] lemma zero_re : (0 : Complexification E).re = 0 := rfl
@[simp] lemma zero_im : (0 : Complexification E).im = 0 := rfl
@[simp] lemma add_re (p q : Complexification E) : (p + q).re = p.re + q.re := rfl
@[simp] lemma add_im (p q : Complexification E) : (p + q).im = p.im + q.im := rfl
@[simp] lemma neg_re (p : Complexification E) : (-p).re = -p.re := rfl
@[simp] lemma neg_im (p : Complexification E) : (-p).im = -p.im := rfl
@[simp] lemma sub_re (p q : Complexification E) : (p - q).re = p.re - q.re := rfl
@[simp] lemma sub_im (p q : Complexification E) : (p - q).im = p.im - q.im := rfl

instance : AddCommGroup (Complexification E) where
  add_assoc _ _ _ := by ext <;> simp [add_assoc]
  zero_add _ := by ext <;> simp
  add_zero _ := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel _ := by ext <;> simp
  add_comm _ _ := by ext <;> simp [add_comm]
  sub_eq_add_neg _ _ := by ext <;> simp [sub_eq_add_neg]

/-! ## Topology (product topology via re and im) -/

instance [TopologicalSpace E] : TopologicalSpace (Complexification E) :=
  TopologicalSpace.induced Complexification.re ‹_› ⊓
  TopologicalSpace.induced Complexification.im ‹_›

/-! ## Complex scalar action: (a + bi) • (f, g) = (af - bg, ag + bf) -/

variable [Module ℝ E]

instance : SMul ℂ (Complexification E) where
  smul z p := ⟨z.re • p.re - z.im • p.im, z.re • p.im + z.im • p.re⟩

@[simp] lemma smul_re (z : ℂ) (p : Complexification E) :
    (z • p).re = z.re • p.re - z.im • p.im := rfl
@[simp] lemma smul_im (z : ℂ) (p : Complexification E) :
    (z • p).im = z.re • p.im + z.im • p.re := rfl

instance : Module ℂ (Complexification E) where
  one_smul p := by
    ext <;> simp [Complex.one_re, Complex.one_im]
  mul_smul z w p := by
    ext <;> simp [Complex.mul_re, Complex.mul_im, mul_smul,
      smul_sub, smul_add, sub_smul, add_smul] <;> abel
  smul_zero z := by
    ext <;> simp
  smul_add z p q := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im, smul_add] <;> abel
  add_smul z w p := by
    ext <;> simp [Complex.add_re, Complex.add_im, add_smul] <;> abel
  zero_smul p := by
    ext <;> simp [Complex.zero_re, Complex.zero_im]

/-! ## Real embedding: f ↦ f + i·0 -/

omit [Module ℝ E] in
/-- Embed a real vector into its complexification. -/
def ofReal (f : E) : Complexification E := ⟨f, 0⟩

omit [Module ℝ E] in
@[simp] lemma ofReal_re (f : E) : (ofReal f).re = f := rfl
omit [Module ℝ E] in
@[simp] lemma ofReal_im (f : E) : (ofReal f).im = 0 := rfl

omit [Module ℝ E] in
/-- The imaginary embedding: g ↦ 0 + i·g. -/
def ofImag (g : E) : Complexification E := ⟨0, g⟩

omit [Module ℝ E] in
@[simp] lemma ofImag_re (g : E) : (ofImag g).re = 0 := rfl
omit [Module ℝ E] in
@[simp] lemma ofImag_im (g : E) : (ofImag g).im = g := rfl

/-- Every element decomposes as ofReal(re) + I • ofReal(im). -/
lemma decompose (p : Complexification E) :
    p = ofReal p.re + Complex.I • ofReal p.im := by
  ext
  · simp [ofReal, Complex.I_re, Complex.I_im]
  · simp [ofReal, Complex.I_re, Complex.I_im]

end Complexification

/-! ## Schwartz space isomorphism

The complexification of SchwartzMap D ℝ is ℂ-linearly isomorphic to SchwartzMap D ℂ
via (f, g) ↦ (x ↦ f(x) + i·g(x)). This validates the euclidean spacetime's
choice of TestFunℂ := SchwartzMap D ℂ as equivalent to the complexification
used for cylinder/torus spacetimes. -/

section SchwartzComplexification

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- Auxiliary: bound on iterated derivative of CLM composed with Schwartz function. -/
private theorem norm_iteratedFDeriv_clm_comp_schwartz
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : SchwartzMap E F) (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ n (L ∘ ⇑f) x‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n f x‖ :=
  L.norm_iteratedFDeriv_comp_left (f.smooth ⊤).contDiffAt (mod_cast le_top)

/-- Post-compose a real-valued Schwartz map with `Complex.ofRealCLM` to get a
ℂ-valued Schwartz map. This is ℝ-linear. -/
private noncomputable def schwartzOfReal (f : SchwartzMap D ℝ) : SchwartzMap D ℂ :=
  ⟨fun x => ↑(f x), Complex.ofRealCLM.contDiff.comp (f.smooth _), fun k n => by
    rcases f.decay k n with ⟨C, hC, hbound⟩
    refine ⟨C, fun x => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ ⇑f) x‖
        ≤ ‖x‖ ^ k * (‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n f x‖) := by
          gcongr; exact norm_iteratedFDeriv_clm_comp_schwartz _ _ _ _
        _ ≤ C := by rw [Complex.ofRealCLM_norm, one_mul]; exact hbound x⟩

/-- Extract the real part of a ℂ-valued Schwartz map. -/
private noncomputable def schwartzRe (f : SchwartzMap D ℂ) : SchwartzMap D ℝ :=
  ⟨fun x => (f x).re, Complex.reCLM.contDiff.comp (f.smooth _), fun k n => by
    rcases f.decay k n with ⟨C, hC, hbound⟩
    refine ⟨C, fun x => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.reCLM ∘ ⇑f) x‖
        ≤ ‖x‖ ^ k * (‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ n f x‖) := by
          gcongr; exact norm_iteratedFDeriv_clm_comp_schwartz _ _ _ _
        _ ≤ C := by rw [Complex.reCLM_norm, one_mul]; exact hbound x⟩

/-- Extract the imaginary part of a ℂ-valued Schwartz map. -/
private noncomputable def schwartzIm (f : SchwartzMap D ℂ) : SchwartzMap D ℝ :=
  ⟨fun x => (f x).im, Complex.imCLM.contDiff.comp (f.smooth _), fun k n => by
    rcases f.decay k n with ⟨C, hC, hbound⟩
    refine ⟨C, fun x => ?_⟩
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Complex.imCLM ∘ ⇑f) x‖
        ≤ ‖x‖ ^ k * (‖Complex.imCLM‖ * ‖iteratedFDeriv ℝ n f x‖) := by
          gcongr; exact norm_iteratedFDeriv_clm_comp_schwartz _ _ _ _
        _ ≤ C := by rw [Complex.imCLM_norm, one_mul]; exact hbound x⟩

/-- The complexification of real Schwartz space is ℂ-linearly isomorphic
to complex Schwartz space via (f, g) ↦ (x ↦ f(x) + ig(x)).

The proof requires showing: (1) the map preserves Schwartz decay
(from ‖a + bi‖ ≤ |a| + |b|), (2) the inverse preserves decay
(from |re z| ≤ ‖z‖), (3) both are ℂ-linear, and (4) both are
continuous in the Schwartz topology (from seminorm equivalence). -/
noncomputable def schwartzComplexificationEquiv :
    Complexification (SchwartzMap D ℝ) ≃ₗ[ℂ] SchwartzMap D ℂ :=
  { toFun := fun p => schwartzOfReal p.re + Complex.I • schwartzOfReal p.im
    invFun := fun f => ⟨schwartzRe f, schwartzIm f⟩
    left_inv := fun p => by
      ext x
      · show (↑(p.re x) + Complex.I * ↑(p.im x)).re = p.re x
        simp
      · show (↑(p.re x) + Complex.I * ↑(p.im x)).im = p.im x
        simp
    right_inv := fun f => by
      ext x
      show ↑(f x).re + Complex.I * ↑(f x).im = f x
      rw [mul_comm]
      exact Complex.re_add_im (f x)
    map_add' := fun p q => by
      ext x
      show ↑((p.re + q.re) x) + Complex.I * ↑((p.im + q.im) x) =
        (↑(p.re x) + Complex.I * ↑(p.im x)) + (↑(q.re x) + Complex.I * ↑(q.im x))
      simp only [SchwartzMap.add_apply, Complex.ofReal_add]
      ring
    map_smul' := fun z p => by
      ext x
      show ↑(z.re • p.re x - z.im • p.im x) +
        Complex.I * ↑(z.re • p.im x + z.im • p.re x) =
        z * (↑(p.re x) + Complex.I * ↑(p.im x))
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.I_re, Complex.I_im, smul_eq_mul] }

end SchwartzComplexification

end GaussianField
