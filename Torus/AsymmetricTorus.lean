/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Torus Test Function Space

Defines the asymmetric torus T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ) test function
space as a tensor product of circle spaces with different periods.

This is the starting point for Route B': the UV limit on the asymmetric torus
followed by the IR limit Lt → ∞ to the cylinder S¹_Ls × ℝ.

## Main definitions

- `AsymTorusTestFunction Lt Ls` — smooth functions on T_{Lt,Ls}
- `AsymLatticeSites Nt Ns` — lattice sites (ℤ/Nt ℤ) × (ℤ/Ns ℤ)
- `evalAsymTorusAtSite` — evaluation at an asymmetric lattice site
- `asymTorusEmbedCLM` — lattice field → torus configuration embedding
- `asymTorusTranslation` — translation on the asymmetric torus

## Design

The `NuclearTensorProduct` infrastructure is already generic in its two factor
spaces, so `AsymTorusTestFunction Lt Ls` inherits all NTP operations
(evalCLM, mapCLM, pure, basisVec, seminorms) without any changes.

The symmetric torus `TorusTestFunction L` is the special case `Lt = Ls = L`.

## References

- Glimm-Jaffe, *Quantum Physics*, Chapter 19
- Simon, *The P(φ)₂ Euclidean QFT*, Chapter VIII
-/

import Torus.Restriction
import Torus.Symmetry

noncomputable section

namespace GaussianField

open NuclearTensorProduct

variable (Lt Ls : ℝ) [hLt : Fact (0 < Lt)] [hLs : Fact (0 < Ls)]

/-! ## Asymmetric torus test function space -/

/-- The test function space for the asymmetric torus T_{Lt,Ls} = (ℝ/Lt ℤ) × (ℝ/Ls ℤ).

This is the nuclear tensor product C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls}), modeling smooth
functions that are Lt-periodic in the first (time) variable and Ls-periodic in
the second (space) variable. -/
abbrev AsymTorusTestFunction :=
  NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)

-- Inherits DyninMityaginSpace
example : DyninMityaginSpace (AsymTorusTestFunction Lt Ls) := inferInstance

/-- The symmetric torus is the special case Lt = Ls. -/
theorem asymTorus_eq_symmetric (L : ℝ) [Fact (0 < L)] :
    AsymTorusTestFunction L L = TorusTestFunction L := rfl

/-! ## Asymmetric lattice sites -/

/-- Lattice sites for the asymmetric torus: (ℤ/Nt ℤ) × (ℤ/Ns ℤ).

Unlike `FinLatticeSites 2 N = Fin 2 → ZMod N` which forces both dimensions
to have the same number of sites, this allows Nt ≠ Ns. -/
abbrev AsymLatticeSites (Nt Ns : ℕ) := ZMod Nt × ZMod Ns

/-- Lattice field on the asymmetric lattice. -/
abbrev AsymLatticeField (Nt Ns : ℕ) := AsymLatticeSites Nt Ns → ℝ

instance (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] : Fintype (AsymLatticeSites Nt Ns) :=
  instFintypeProd _ _

/-! ## Evaluation at asymmetric lattice sites -/

/-- Evaluation of an asymmetric torus test function at a lattice site.

For `f ∈ C∞(S¹_{Lt}) ⊗̂ C∞(S¹_{Ls})`, the evaluation at site `(i, j)` is:

  `eval_{(i,j)}(f) = (r_{Nt}(·)(i) ⊗ r_{Ns}(·)(j))(f)`

where `r_{Nt}` restricts to the time lattice with spacing Lt/Nt and
`r_{Ns}` restricts to the space lattice with spacing Ls/Ns.

For a pure tensor `f_t ⊗ f_s`:
  `eval_{(i,j)}(f_t ⊗ f_s) = √(Lt/Nt) · f_t(i·Lt/Nt) · √(Ls/Ns) · f_s(j·Ls/Ns)` -/
def evalAsymTorusAtSite (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (x : AsymLatticeSites Nt Ns) : AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
  let proj_t : (ZMod Nt → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj x.1
  let proj_s : (ZMod Ns → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj x.2
  evalCLM
    (proj_t.comp (circleRestriction Lt Nt))
    (proj_s.comp (circleRestriction Ls Ns))

/-! ## Lattice-to-torus embedding -/

/-- The asymmetric torus embedding: maps a lattice field
`φ : (ℤ/Nt ℤ) × (ℤ/Ns ℤ) → ℝ` to a configuration on the asymmetric torus.

  `(ι φ)(f) = Σ_{x ∈ lattice} φ(x) · eval_x(f)` -/
def asymTorusEmbedCLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    Configuration (AsymTorusTestFunction Lt Ls) where
  toFun f := ∑ x : AsymLatticeSites Nt Ns,
    φ x * evalAsymTorusAtSite Lt Ls Nt Ns x f
  map_add' f g := by simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [map_smul, smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
  cont := by
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (evalAsymTorusAtSite Lt Ls Nt Ns x).cont

@[simp] theorem asymTorusEmbedCLM_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) (f : AsymTorusTestFunction Lt Ls) :
    asymTorusEmbedCLM Lt Ls Nt Ns φ f =
    ∑ x : AsymLatticeSites Nt Ns,
      φ x * evalAsymTorusAtSite Lt Ls Nt Ns x f :=
  rfl

/-! ## Translation on the asymmetric torus -/

/-- Translation on the asymmetric torus T_{Lt,Ls}.

Translates the time variable by `v.1` (period Lt) and
the space variable by `v.2` (period Ls). -/
def asymTorusTranslation (v : ℝ × ℝ) :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  nuclearTensorProduct_mapCLM
    (circleTranslation Lt v.1)
    (circleTranslation Ls v.2)

/-! ## Time reflection on the asymmetric torus -/

/-- Time reflection Θ: (t, x) ↦ (-t, x) on the asymmetric torus.

Acts by `circleReflection` on the time factor and identity on the space factor.
This is the key symmetry for reflection positivity (OS3). -/
def asymTorusTimeReflection :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymTorusTestFunction Lt Ls :=
  nuclearTensorProduct_mapCLM
    (circleReflection Lt)
    (ContinuousLinearMap.id ℝ _)

/-! ## Coordinate swap -/

/-- Swap of coordinates (t, x) ↦ (x, t) on the asymmetric torus.

Note: this maps `AsymTorusTestFunction Lt Ls` to `AsymTorusTestFunction Ls Lt`,
swapping the two periods. This is NOT an endomorphism when Lt ≠ Ls. -/
def asymTorusSwap :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymTorusTestFunction Ls Lt :=
  nuclearTensorProduct_swapCLM

end GaussianField
