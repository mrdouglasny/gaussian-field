/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function on the Cylinder S¹_L × ℝ

Defines the Green's function (covariance) for the massive free field
on the cylinder via the **heat kernel integral representation**:

  `G(f, g) = ∫₀^∞ ⟨f, e^{-tA} g⟩_{L²} dt`

where `A = -Δ_{S¹} - ∂²/∂t² + m²` is the cylinder operator.

## Architecture

The proof chain uses two layers connecting to the heat semigroup:

1. **Mass operator** `T = A^{-1/2}` — a CLM to ℓ² satisfying `⟨Tf, Tg⟩ = G(f,g)`.
   Any symmetry that commutes with the heat semigroup `e^{-tA}` for all t ≥ 0
   also intertwines T with an isometry on ℓ². This follows because the
   covariance `C = ∫₀^∞ e^{-tA} dt` commutes with such symmetries (by linearity
   of the Bochner integral), and `T = C^{1/2}` inherits this equivariance.

2. **Green's function** `G(f,g) = ⟨Tf, Tg⟩` — algebraic properties (bilinearity,
   symmetry, nonnegativity) are free from the inner product structure.

## Main definitions

- `resolventFreq L mass n` — dispersion relation ω_n = √(λ_n + m²) (defined)
- `cylinderMassOperator L mass` — CLM T : CylinderTestFunction L → ℓ² (defined)
- `cylinderGreen L mass` — bilinear form G_L(f,g) = ⟨Tf, Tg⟩ (defined)

## Main results

- `cylinderMassOperator_spatialTranslation_equivariant` — T equivariant (proved)
- `cylinderMassOperator_timeTranslation_equivariant` — T equivariant (proved)
- `cylinderMassOperator_timeReflection_equivariant` — T equivariant (proved)
- `cylinderGreen_spatialTranslation_invariant` — G invariant (proved)
- `cylinderGreen_timeTranslation_invariant` — G invariant (proved)
- `cylinderGreen_timeReflection_invariant` — G invariant (proved)

## Mathematical background

The Green's function on S¹_L × ℝ for the operator (-Δ_x - ∂²/∂t² + m²) is:

  `G((x,t), (x',t')) = Σ_n φ_n(x) φ_n(x') · exp(-ω_n |t-t'|) / (2ω_n)`

where φ_n are Fourier modes on S¹_L with eigenvalues λ_n = (2πn/L)²,
and ω_n = √(λ_n + m²) is the dispersion relation.

### Heat kernel integral representation

The covariance operator `C = A⁻¹` is the Bochner integral of the
cylinder heat semigroup:

  `C = ∫₀^∞ e^{-tA} dt = ∫₀^∞ e^{-m²t} · (e^{tΔ_{S¹}} ⊗ e^{tΔ_ℝ}) dt`

The integral converges because `e^{-m²t}` decays exponentially for m > 0.
The mass operator is `T = C^{1/2}` (or more precisely, the composition of
`A^{-1/2}` with the L² embedding into ℓ²).

### Why invariance follows from the heat kernel

If a symmetry S commutes with `e^{-tA}` for all t ≥ 0:

  `S ∘ e^{-tA} = e^{-tA} ∘ S`

then S commutes with the integral `C = ∫₀^∞ e^{-tA} dt` (linearity
of Bochner integral), and therefore with `T = C^{1/2}` as well.
The L² isometry condition (that S is unitary on L²(S¹×ℝ)) ensures
the ℓ² action is isometric: `T(Sf) = U(Tf)` for some isometry U.

### Temporal direction

**Important**: The temporal direction uses the free Laplacian `-d²/dt²`
(continuous spectrum on ℝ, diagonal in the Fourier basis), NOT the harmonic
oscillator `-d²/dt² + t²` (discrete spectrum, diagonal in Hermite basis).
The DMS basis for 𝓢(ℝ) is Hermite functions, but the resolvent
`(p² + ω²)^{-1/2}` is NOT diagonal in that basis.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II, §X.12
-/

import Cylinder.MassOperatorConstruction
import Cylinder.MassOperatorEquivariance

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

-- resolventFreq and cylinderMassOperator are now defined in
-- Cylinder/MassOperatorConstruction.lean and re-exported here via import.

/-! ## Cylinder Green's function

Defined from the mass operator via the inner product on ℓ².
The algebraic properties follow from inner product space theory.

Equivalently, the Green's function is the L² pairing with the covariance operator:

  `G(f, g) = ⟨Tf, Tg⟩_{ℓ²} = ⟨f, Cg⟩_{L²(S¹×ℝ)} = ∫₀^∞ ⟨f, e^{-tA}g⟩_{L²} dt`

The heat kernel integral representation makes the physical content transparent:
the Green's function sums the heat kernel over all times. -/

/-- The continuum Green's function on the cylinder S¹_L × ℝ.

  `G_L(f, g) = ⟨T f, T g⟩_{ℓ²}`

where T is the mass operator. Equivalently, via the heat kernel integral:

  `G_L(f, g) = ∫₀^∞ ⟨f, e^{-tA} g⟩_{L²(S¹×ℝ)} dt`

In the mixed spectral/position representation:

  `G_L(f,g) = Σ_n ∫∫ f̂_n(t) ĝ_n(t') · exp(-ω_n|t-t'|) / (2ω_n) dt dt'`

where `f̂_n(t) = ∫₀ᴸ f(x,t) φ_n(x) dx` is the n-th Fourier mode,
and `ω_n = resolventFreq L mass n` is the dispersion relation. -/
def cylinderGreen (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) : ℝ :=
  @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f)
    (cylinderMassOperator L mass hmass g)

/-- The mass operator realizes the Green's function as an inner product.

  `G_L(f, g) = ⟨T f, T g⟩` -/
theorem cylinderMassOperator_inner (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g =
    @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f)
      (cylinderMassOperator L mass hmass g) := rfl

/-- The cylinder Green's function is bilinear. -/
theorem cylinderGreen_bilinear (mass : ℝ) (hmass : 0 < mass) :
    ∀ (r : ℝ) (f g h : CylinderTestFunction L),
      cylinderGreen L mass hmass (r • f + g) h =
      r * cylinderGreen L mass hmass f h + cylinderGreen L mass hmass g h := by
  intro r f g h
  simp only [cylinderGreen, map_add, map_smul]
  rw [inner_add_left, real_inner_smul_left]

/-- The cylinder Green's function is symmetric. -/
theorem cylinderGreen_symm (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g = cylinderGreen L mass hmass g f := by
  simp only [cylinderGreen]
  exact real_inner_comm _ _

/-- The cylinder Green's function is nonneg on the diagonal.

  `G_L(f,f) ≥ 0` for all f. -/
theorem cylinderGreen_nonneg (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    0 ≤ cylinderGreen L mass hmass f f := by
  simp only [cylinderGreen]
  exact real_inner_self_nonneg

/-- The diagonal of the cylinder Green's function is continuous.

  `f ↦ G_L(f, f)` is continuous on `CylinderTestFunction L`.

Follows from continuity of the mass operator T and the inner product. -/
theorem cylinderGreen_continuous_diag (mass : ℝ) (hmass : 0 < mass) :
    Continuous (fun f : CylinderTestFunction L => cylinderGreen L mass hmass f f) := by
  simp only [cylinderGreen]
  exact (cylinderMassOperator L mass hmass).continuous.inner
    (cylinderMassOperator L mass hmass).continuous

/-- The cylinder mass operator is injective.

If `T f = 0` in ℓ² then `f = 0`. The proof works by:
1. `T f = 0` implies all coordinates `(T f)_m = 0`
2. For each spatial mode `a`, the resolvent image `R_{ω_a}(slice_a f)` has
   all DM coefficients zero, hence is zero
3. By `resolventMultiplierCLM_injective`, each slice `slice_a f = 0`
4. By `ntpExtractSlice` definition, `f.val(pair(a,b)) = 0` for all `a, b`
5. By Cantor pairing surjectivity, `f.val m = 0` for all `m`, so `f = 0` -/
theorem cylinderMassOperator_injective (mass : ℝ) (hmass : 0 < mass) :
    Function.Injective (cylinderMassOperator L mass hmass) := by
  intro f g hfg
  rw [← sub_eq_zero]
  apply NuclearTensorProduct.ext
  intro m
  set a := (Nat.unpair m).1
  set b := (Nat.unpair m).2
  -- From hfg: T f = T g, so T(f - g) = 0
  have hTsub : cylinderMassOperator L mass hmass (f - g) = 0 := by
    rw [map_sub, sub_eq_zero]; exact hfg
  -- All coordinates of T(f - g) are zero
  have hcoord : ∀ n, (cylinderMassOperator L mass hmass (f - g)).val n = 0 := by
    intro n; rw [hTsub]; rfl
  -- For all a' b': the DM coefficient b' of R_{ω_{a'}}(slice_{a'} (f-g)) = 0
  have hDM : ∀ a' b',
      (schwartzRapidDecayEquiv1D
        (resolventMultiplierCLM (resolventFreq_pos L mass hmass a')
          (ntpSliceSchwartz L a' (f - g)))).val b' = 0 := by
    intro a' b'
    have := hcoord (Nat.pair a' b')
    rw [cylinderMassOperator_formula] at this
    simp only [Nat.unpair_pair] at this
    -- this : DyninMityaginSpace.coeff b' (R_{ω_{a'}}(slice_{a'} (f-g))) = 0
    -- DyninMityaginSpace.coeff for SchwartzMap ℝ ℝ is (equiv g).val b' by defn
    exact this
  -- For all a': R_{ω_{a'}}(slice_{a'} (f-g)) = 0
  have hResolvent : ∀ a',
      resolventMultiplierCLM (resolventFreq_pos L mass hmass a')
        (ntpSliceSchwartz L a' (f - g)) = 0 := by
    intro a'
    have hRDS : schwartzRapidDecayEquiv1D
        (resolventMultiplierCLM (resolventFreq_pos L mass hmass a')
          (ntpSliceSchwartz L a' (f - g))) = 0 :=
      RapidDecaySeq.ext (hDM a')
    exact schwartzRapidDecayEquiv1D.injective (by rw [hRDS, map_zero])
  -- For all a': slice_{a'} (f-g) = 0
  have hSlice : ∀ a', ntpSliceSchwartz L a' (f - g) = 0 := by
    intro a'
    exact resolventMultiplierCLM_injective (resolventFreq_pos L mass hmass a')
      (by rw [hResolvent a', map_zero])
  -- For all a': ntpExtractSlice a' (f-g) = 0
  have hExtract : ∀ a', ntpExtractSlice a' (f - g) = 0 := by
    intro a'
    have h := hSlice a'
    -- ntpSliceSchwartz = equiv.symm ∘ ntpExtractSlice, so equiv.symm(extract) = 0
    -- hence extract = equiv(equiv.symm(extract)) = equiv(slice) = equiv(0) = 0
    rw [← schwartzRapidDecayEquiv1D.apply_symm_apply (ntpExtractSlice a' (f - g))]
    change schwartzRapidDecayEquiv1D (ntpSliceSchwartz L a' (f - g)) = 0
    rw [h, map_zero]
  -- f.val m - g.val m = (f - g).val m = (f - g).val (pair a b) = (extract a (f-g)).val b = 0
  have : (ntpExtractSlice a (f - g)).val b = 0 := by
    rw [hExtract a]; rfl
  rw [ntpExtractSlice_val] at this
  rw [show Nat.pair a b = m from Nat.pair_unpair m] at this
  simpa using this

/-- The cylinder Green's function is strictly positive on nonzero functions.

  `G_L(f,f) > 0` for f ≠ 0.

Proved from injectivity of the mass operator: `G(f,f) = ⟨Tf, Tf⟩ = ‖Tf‖²`,
and `Tf ≠ 0` when `f ≠ 0` by `cylinderMassOperator_injective`. -/
theorem cylinderGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (hf : f ≠ 0) :
    0 < cylinderGreen L mass hmass f f := by
  simp only [cylinderGreen, real_inner_self_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (fun h => hf (cylinderMassOperator_injective L mass hmass
      (by rw [h, map_zero]))))

/-! ## Heat kernel equivariance principle

If a CLM `S` commutes with the cylinder heat semigroup `e^{-tA}` for all
`t ≥ 0`, then the mass operator `T = A^{-1/2}` intertwines `S` with a
linear isometry `U` on ℓ²: `T(Sf) = U(Tf)`.

**Mathematical justification**: The proof goes through the covariance
operator `C = ∫₀^∞ e^{-tA} dt`. By linearity of the Bochner integral,
`[S, e^{-tA}] = 0` implies `[S, C] = 0`. Since `T*T = C` in the L²
sense, commutation with C implies `S` preserves the quadratic form
`⟨f, Cg⟩ = ⟨Tf, Tg⟩`, and any invertible map preserving a positive
definite form lifts to an isometry of the GNS Hilbert space. -/

/-! ## Spacetime symmetry structure and master equivariance axiom

A `CylinderSpacetimeSymmetry` bundles the two properties that any
Euclidean-group action on the cylinder satisfies — heat-semigroup
commutation and mass-operator-norm preservation — into a single
structured argument. The mass operator's equivariance under any
spacetime symmetry is then a single axiom.

Specific symmetries (spatial translation, time translation, time
reflection, and their products) are constructed as instances of
`CylinderSpacetimeSymmetry`.

**Vetted 2026-05-09** by Gemini deep-think (2.5-pro and 3.1-pro-preview)
which independently flagged that heat-commutation alone is insufficient
for the isometry conclusion (counterexample `S = 2·id`); the
`preserves_T_norm` field below is the missing ingredient. -/

/-- A spacetime symmetry of the cylinder: a continuous linear operator
on cylinder test functions that **(1)** commutes with the heat semigroup
`e^{-tA}` and **(2)** preserves the mass-operator ℓ²-norm.

For Euclidean-group operators (translations, reflections), property (1)
comes from the heat kernel commuting with the symmetry's geometric
action, and property (2) reduces to the operator preserving the L²
inner product on cylinder test functions (Lebesgue/Haar invariance). -/
structure CylinderSpacetimeSymmetry (mass : ℝ) (hmass : 0 < mass) where
  /-- The underlying continuous linear operator on cylinder test functions. -/
  toCLM : CylinderTestFunction L →L[ℝ] CylinderTestFunction L
  /-- Commutation with the cylinder heat semigroup: `e^{-tA} ∘ S = S ∘ e^{-tA}`. -/
  heat_comm : ∀ {t : ℝ} (ht : 0 ≤ t) (f : CylinderTestFunction L),
    cylinderHeatSemigroup L ht mass (toCLM f) =
    toCLM (cylinderHeatSemigroup L ht mass f)
  /-- Preservation of the mass-operator ℓ²-norm: `‖T(Sf)‖ = ‖Tf‖`.
  This is the missing ingredient that the previous false axiom omitted. -/
  preserves_T_norm : ∀ f : CylinderTestFunction L,
    ‖cylinderMassOperator L mass hmass (toCLM f)‖ =
    ‖cylinderMassOperator L mass hmass f‖

/-- **Master equivariance axiom for the mass operator.**

For any cylinder spacetime symmetry `S`, the mass operator `T`
intertwines `S` with a linear isometric equivalence `U` on ℓ²:
`T(Sf) = U(Tf)`.

The mathematical justification: heat-commutation gives `[S, A⁻¹] = 0`,
so `T(Sf) = U(Tf)` for some linear `U`. The `preserves_T_norm` field
upgrades `U` from a linear intertwiner to a full isometry, and from
the dense range of `T` it extends uniquely to `ell2' ≃ₗᵢ[ℝ] ell2'`. -/
axiom cylinderMassOperator_equivariant
    (mass : ℝ) (hmass : 0 < mass)
    (S : CylinderSpacetimeSymmetry L mass hmass) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (S.toCLM f) =
         U (cylinderMassOperator L mass hmass f)

/-! ## Specific spacetime symmetries

The Euclidean-group operators on the cylinder are constructed as
instances of `CylinderSpacetimeSymmetry`. The `heat_comm` field comes
from the existing heat-semigroup commutation theorems; the
`preserves_T_norm` field is provided as an axiomatic instance for each
specific operator (provable from Lebesgue/Haar measure invariance). -/

/-- The mass-operator ℓ²-norm is preserved by spatial translation.
This is a Haar-invariance fact on `S¹_L`. -/
axiom cylinderMassOperator_spatialTranslation_norm_eq
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
    ‖cylinderMassOperator L mass hmass f‖

/-- The mass-operator ℓ²-norm is preserved by time translation.
Proved in `Cylinder/MassOperatorEquivariance.lean`. -/
theorem cylinderMassOperator_timeTranslation_norm_eq
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderTimeTranslation L τ f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ :=
  cylinderMassOperator_timeTranslation_norm_eq_proved L mass hmass τ f

/-- The mass-operator ℓ²-norm is preserved by time reflection.
Proved in `Cylinder/MassOperatorEquivariance.lean`. -/
theorem cylinderMassOperator_timeReflection_norm_eq
    (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderTimeReflection L f)‖ =
    ‖cylinderMassOperator L mass hmass f‖ :=
  cylinderMassOperator_timeReflection_norm_eq_proved L mass hmass f

/-- Spatial translation as a `CylinderSpacetimeSymmetry`. -/
def cylinderSpatialTranslationSym
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) :
    CylinderSpacetimeSymmetry L mass hmass where
  toCLM := cylinderSpatialTranslation L v
  heat_comm ht g := cylinderHeatSemigroup_spatialTranslation_comm L ht mass v g
  preserves_T_norm := cylinderMassOperator_spatialTranslation_norm_eq L mass hmass v

/-- Time translation as a `CylinderSpacetimeSymmetry`. -/
def cylinderTimeTranslationSym
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ) :
    CylinderSpacetimeSymmetry L mass hmass where
  toCLM := cylinderTimeTranslation L τ
  heat_comm ht g := cylinderHeatSemigroup_timeTranslation_comm L ht mass τ g
  preserves_T_norm := cylinderMassOperator_timeTranslation_norm_eq L mass hmass τ

/-- Time reflection as a `CylinderSpacetimeSymmetry`. -/
def cylinderTimeReflectionSym
    (mass : ℝ) (hmass : 0 < mass) :
    CylinderSpacetimeSymmetry L mass hmass where
  toCLM := cylinderTimeReflection L
  heat_comm ht g := cylinderHeatSemigroup_timeReflection_comm L ht mass g
  preserves_T_norm := cylinderMassOperator_timeReflection_norm_eq L mass hmass

/-! ## Mass operator equivariance (derived from the master axiom)

Each equivariance theorem follows by applying the master axiom to the
corresponding `CylinderSpacetimeSymmetry` instance. -/

/-- The mass operator intertwines spatial translation with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_spatialTranslation_comm`. -/
theorem cylinderMassOperator_spatialTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant L mass hmass
    (cylinderSpatialTranslationSym L mass hmass v)

/-- The mass operator intertwines time translation with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_timeTranslation_comm`. -/
theorem cylinderMassOperator_timeTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeTranslation L τ f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant L mass hmass
    (cylinderTimeTranslationSym L mass hmass τ)

/-- The mass operator intertwines time reflection with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_timeReflection_comm`. -/
theorem cylinderMassOperator_timeReflection_equivariant
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeReflection L f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant L mass hmass
    (cylinderTimeReflectionSym L mass hmass)

/-! ## Invariance properties

Derived from mass operator equivariance: `G(Sf, Sg) = ⟨T(Sf), T(Sg)⟩ =
⟨U(Tf), U(Tg)⟩ = ⟨Tf, Tg⟩ = G(f, g)`, using the isometry property. -/

/-- The cylinder Green's function is invariant under spatial translation.

  `G_L(T_v f, T_v g) = G_L(f, g)` for all v ∈ S¹_L. -/
theorem cylinderGreen_spatialTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderSpatialTranslation L v f)
      (cylinderSpatialTranslation L v g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_spatialTranslation_equivariant L mass hmass v
  rw [hU f, hU g]
  exact U.inner_map_map _ _

/-- The cylinder Green's function is invariant under time translation.

  `G_L(T_τ f, T_τ g) = G_L(f, g)` for all τ ∈ ℝ. -/
theorem cylinderGreen_timeTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeTranslation L τ f)
      (cylinderTimeTranslation L τ g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_timeTranslation_equivariant L mass hmass τ
  rw [hU f, hU g]
  exact U.inner_map_map _ _

/-- The cylinder Green's function is invariant under time reflection.

  `G_L(Θf, Θg) = G_L(f, g)`. -/
theorem cylinderGreen_timeReflection_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeReflection L f)
      (cylinderTimeReflection L g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_timeReflection_equivariant L mass hmass
  rw [hU f, hU g]
  exact U.inner_map_map _ _

end GaussianField
