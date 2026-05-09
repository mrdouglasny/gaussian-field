/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Wick Polynomials in the Eigenbasis

Identifies multivariate Wick polynomials in the lattice GFF with
multivariate Hermite polynomials in the eigenbasis-orthogonalized
coordinates `(ξ_k)` from `GaussianField/StandardGaussianBridge.lean`.

The setup: the lattice GFF measure pushes forward via
`gffOrthonormalProj` to the standard multivariate Gaussian
`Π_k gaussianReal 0 1`. Under this change of variables, multivariate
Wick polynomials become multivariate Hermite polynomials, since:

* Each `ξ_k` is standard `N(0,1)` (variance 1).
* The 1D Wick monomial of variance 1 equals the probabilist's Hermite
  polynomial: `:x^n:_1 = He_n(x)` (consequence of `wick_eq_hermiteR`
  in `SchwartzNuclear/HermiteWick.lean`).
* Independence of distinct `ξ_k` makes
  `:ξ^α:_1 := ∏_k :ξ_k^{α_k}:_1` a multivariate Wick monomial that is
  also a multivariate Hermite polynomial.

The site Wick monomial `:φ(x)^d:_{c_a}` then admits an explicit
expansion in eigenbasis multi-indices, giving the chaos decomposition
of the GFF interaction.

## Main definitions

- `gffMultiWickMonomial` — multivariate Wick monomial indexed by a
  multi-index over eigenbasis sites.
- `gffMultiHermiteValue` — multivariate Hermite polynomial in the
  orthogonalized variables (purely as a function of `ω`).

## Main theorems

- `gffMultiWickMonomial_eq_hermiteMulti` — the two coincide.
- `siteWickMonomial_eigenbasis_expansion` — site Wick monomial as an
  explicit linear combination of `gffMultiWickMonomial`s.
- `interaction_centered_in_chaosLE` — the GFF interaction
  $V_a - \mathbb E V_a$ is a finite linear combination of Wick
  monomials of total degree $\le \deg P$, hence (after the change of
  variables) lies in `wienerChaosLE _ (deg P)`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §3.1
  (Hermite polynomials) and Theorem 3.21 (orthogonality).
- Glimm and Jaffe, *Quantum Physics*, §6.1 (Wick ordering).
- `SchwartzNuclear/HermiteWick.lean` (this repo) — `wick_eq_hermiteR`,
  the 1D building block.

## Status

API + axiom skeleton (2026-05-08). Definitions are concrete; the
identification theorems are stated as axioms with proof-strategy
docstrings citing the existing 1D infrastructure. QFT-specific
specializations (e.g. interaction polynomial $V_a$ in the chaos)
live downstream in pphi2's `PolynomialChaosBridge.lean`; this file
provides only the generic Gaussian-Hilbert-space identifications.
-/

import GaussianField.StandardGaussianBridge
import GaussianField.Wick
import SchwartzNuclear.HermiteWick
import SchwartzNuclear.HermiteFunctions

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory

variable (d N : ℕ) [NeZero N]

/-- Total degree of a multi-index over `FinLatticeSites d N`. -/
def MultiIndexLattice.totalDegree {d N : ℕ} [NeZero N]
    (α : FinLatticeSites d N → ℕ) : ℕ :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  ∑ k, α k

/-- All multi-indices on `FinLatticeSites d N` with each component
bounded by `D + 1` (so total degree is bounded by `D · |Λ|`).
Constrained per-coordinate because `FinLatticeSites d N → ℕ` is not a
`Fintype`; the constraint gives a finite Finset enumeration via
`Fintype.piFinset`. -/
noncomputable def multiIndicesUpToDegree (d N D : ℕ) [NeZero N] :
    Finset (FinLatticeSites d N → ℕ) :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  haveI : DecidableEq (FinLatticeSites d N) :=
    Classical.decEq (FinLatticeSites d N)
  Fintype.piFinset (fun _ : FinLatticeSites d N => Finset.range (D + 1))

/-- Multi-indices on `FinLatticeSites d N` with total degree exactly `k`
(and each coord in `Finset.range (k + 1)`). -/
noncomputable def multiIndicesOfDegree (d N k : ℕ) [NeZero N] :
    Finset (FinLatticeSites d N → ℕ) :=
  (multiIndicesUpToDegree d N k).filter
    (fun α => MultiIndexLattice.totalDegree α = k)

/-- Multivariate Wick monomial in the orthogonalized GFF coordinates
$(\xi_k)$. For a multi-index $\alpha : \mathrm{FinLatticeSites}\ d\ N
\to \mathbb N$, this is the product of 1D unit-variance Wick monomials:

  `:ξ^α:_1 := ∏_k :ξ_k^{α_k}:_1`.

(All variances are 1 because each `ξ_k` is standard Gaussian under the
lattice GFF pushforward.) -/
noncomputable def gffMultiWickMonomial
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) : ℝ :=
  ∏ k : FinLatticeSites d N,
    wickMonomial (α k) 1 (gffOrthonormalCoord d N a mass ha hmass k ω)

/-- **GFF multivariate Wick monomial = multivariate Hermite in
orthogonalized variables.**

Specifically, since each `ξ_k` is standard `N(0,1)` (variance 1) under
the GFF pushforward, the 1D Wick monomial `:ξ_k^{α_k}:_1` equals the
probabilist's Hermite polynomial $\mathrm{He}_{\alpha_k}(\xi_k)$ by
`wick_eq_hermiteR` (with $c = 1$, $\sqrt c = 1$). Taking the product
over $k$:

  `gffMultiWickMonomial α ω = ∏_k He_{α_k}(ξ_k(ω))`.

This is exactly the multivariate Hermite polynomial of multi-index
$\alpha$ evaluated at the orthogonalized vector. -/
theorem gffMultiWickMonomial_eq_hermite_product
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) :
    gffMultiWickMonomial d N a mass ha hmass α ω =
      ∏ k : FinLatticeSites d N,
        ((Polynomial.hermite (α k)).map (Int.castRingHom ℝ)).eval
          (gffOrthonormalCoord d N a mass ha hmass k ω) := by
  unfold gffMultiWickMonomial
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [wick_eq_hermiteR (α k) 1 (by norm_num : (0:ℝ) < 1)]
  unfold scaledHermite
  rw [Real.sqrt_one, one_pow, one_mul, div_one]

/-- 1D **Wick monomial orthogonality** under the standard Gaussian
`gaussianReal 0 1`:

  `∫ :x^m:_1 · :x^n:_1 ∂γ = δ_{m,n} · m!`.

Reduced to `J_eq` (Hermite L²-inner product against the unnormalized
Gaussian weight) via `wick_eq_hermiteR` (with `c = 1`, `√c = 1`,
`x/√c = x`), then converted from Lebesgue to `gaussianReal 0 1` via
the explicit PDF `(√(2π))⁻¹ · exp(-x²/2)`. -/
theorem wickMonomial_inner_gaussianReal_one (m n : ℕ) :
    ∫ x : ℝ, wickMonomial m 1 x * wickMonomial n 1 x ∂(gaussianReal 0 1) =
    if m = n then (m.factorial : ℝ) else 0 := by
  -- Step 1: wickMonomial k 1 x = (hermiteR k).eval x.
  have h_wick : ∀ (k : ℕ) (x : ℝ),
      wickMonomial k 1 x = (hermiteR k).eval x := by
    intro k x
    rw [wick_eq_hermiteR k 1 (by norm_num : (0:ℝ) < 1)]
    show Real.sqrt 1 ^ k * (hermiteR k).eval (x / Real.sqrt 1) = _
    rw [Real.sqrt_one, one_pow, one_mul, div_one]
  simp_rw [h_wick]
  -- Step 2: Convert gaussianReal 0 1 integral to Lebesgue with the PDF.
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero)]
  simp_rw [smul_eq_mul]
  -- Step 3: Identify gaussianPDFReal 0 1 x = (√(2π))⁻¹ * gaussian x.
  have h_pdf : ∀ x : ℝ,
      gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * gaussian x := by
    intro x
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    show (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x^2 / 2) =
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x^2 / 2))
    congr 2
    ring
  simp_rw [h_pdf]
  -- Step 4: Pull out the (√(2π))⁻¹ constant; what's left is `J m n`.
  rw [show (fun x : ℝ =>
        (Real.sqrt (2 * Real.pi))⁻¹ * gaussian x *
          ((hermiteR m).eval x * (hermiteR n).eval x)) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        ((hermiteR m).eval x * ((hermiteR n).eval x * gaussian x))) from by
    funext x; ring]
  rw [integral_const_mul]
  show (Real.sqrt (2 * Real.pi))⁻¹ * J m n = _
  rw [J_eq n m]
  -- Goal: (√(2π))⁻¹ * (if m = n then m! * √(2π) else 0) = if m = n then m! else 0
  split_ifs with h
  · have h2pi_pos : (0 : ℝ) < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos.mpr (by positivity)
    field_simp
  · ring

/-- **Orthogonality of GFF multivariate Wick monomials under the lattice
GFF measure.**

  `∫ :ξ^α: · :ξ^β: dμ_GFF = δ_{αβ} · ∏_k α_k!`

This is the multivariate Wick orthogonality: distinct multi-indices
give zero, and the diagonal is a product of factorials.

**Proof:** Push forward to `Π_k gaussianReal 0 1` via
`gffOrthonormalProj_pushforward_eq_stdGaussian`, decompose into a
product of 1D integrals via `integral_fintype_prod_eq_prod`, and apply
the 1D orthogonality `wickMonomial_inner_gaussianReal_one` to each
factor. -/
theorem gffMultiWickMonomial_orthogonality
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α β : FinLatticeSites d N → ℕ) :
    ∫ ω, gffMultiWickMonomial d N a mass ha hmass α ω *
        gffMultiWickMonomial d N a mass ha hmass β ω
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (if α = β then ((∏ k, (α k).factorial : ℕ) : ℝ) else 0) := by
  have h_meas := gffOrthonormalProj_measurable d N a mass ha hmass
  -- Helper: each `wickMonomial k 1` is continuous (it's `(hermiteR k).eval`).
  have h_wick_cont : ∀ k : ℕ, Continuous (wickMonomial k 1) := by
    intro k
    have h_eq : (fun x : ℝ => wickMonomial k 1 x) = (hermiteR k).eval := by
      funext x
      rw [wick_eq_hermiteR k 1 (by norm_num : (0:ℝ) < 1)]
      show Real.sqrt 1 ^ k * (hermiteR k).eval (x / Real.sqrt 1) = _
      rw [Real.sqrt_one, one_pow, one_mul, div_one]
    rw [show wickMonomial k 1 = fun x : ℝ => wickMonomial k 1 x from rfl, h_eq]
    exact (hermiteR k).continuous
  -- Step 1: combine the two products into one product of pairs (using the
  -- definitional equality `gffOrthonormalProj ω k = gffOrthonormalCoord k ω`).
  have h_eq : ∀ ω : Configuration (FinLatticeField d N),
      gffMultiWickMonomial d N a mass ha hmass α ω *
        gffMultiWickMonomial d N a mass ha hmass β ω =
      ∏ k, wickMonomial (α k) 1 (gffOrthonormalProj d N a mass ha hmass ω k) *
            wickMonomial (β k) 1 (gffOrthonormalProj d N a mass ha hmass ω k) := by
    intro ω
    unfold gffMultiWickMonomial gffOrthonormalProj
    rw [← Finset.prod_mul_distrib]
  simp_rw [h_eq]
  -- Step 2: Use integral_map and the pushforward equation.
  have h_strong_meas : AEStronglyMeasurable
      (fun y : FinLatticeSites d N → ℝ =>
        ∏ k, wickMonomial (α k) 1 (y k) * wickMonomial (β k) 1 (y k))
      ((latticeGaussianMeasure d N a mass ha hmass).map
        (gffOrthonormalProj d N a mass ha hmass)) := by
    apply Continuous.aestronglyMeasurable
    apply continuous_finset_prod
    intro k _
    exact ((h_wick_cont _).comp (continuous_apply k)).mul
      ((h_wick_cont _).comp (continuous_apply k))
  rw [← integral_map h_meas.aemeasurable
    (f := fun y : FinLatticeSites d N → ℝ =>
      ∏ k, wickMonomial (α k) 1 (y k) * wickMonomial (β k) 1 (y k))
    h_strong_meas]
  rw [gffOrthonormalProj_pushforward_eq_stdGaussian d N a mass ha hmass]
  -- Step 3: apply Fubini to the product over k.
  rw [integral_fintype_prod_eq_prod
    (f := fun k (x : ℝ) => wickMonomial (α k) 1 x * wickMonomial (β k) 1 x)]
  -- Step 4: each factor is the 1D orthogonality.
  simp_rw [wickMonomial_inner_gaussianReal_one]
  -- Step 4: combine the per-coordinate indicators into a single multi-index indicator.
  by_cases hαβ : α = β
  · rw [if_pos hαβ]
    rw [show (∏ k : FinLatticeSites d N,
        if α k = β k then (((α k).factorial : ℕ) : ℝ) else 0) =
        ∏ k : FinLatticeSites d N, ((α k).factorial : ℝ) from by
      refine Finset.prod_congr rfl ?_
      intro k _
      rw [if_pos (by rw [hαβ] : α k = β k)]]
    push_cast
    rfl
  · rw [if_neg hαβ]
    -- Some k has α k ≠ β k, so that factor is 0.
    obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
      by_contra h
      push Not at h
      exact hαβ (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    rw [if_neg hk]

/-- The GFF site (auto-)variance at site `x`:
`c_a(x) = ⟨φ(x), φ(x)⟩ = (a^d)⁻¹ · Σ_k λ_k⁻¹ · e_k(x)²`.

This is the diagonal of the lattice GFF covariance, i.e. the variance
that the local Wick subtraction must subtract for `:φ(x)^k:_{c_a}` to
be the QFT-correct Wick monomial. The site-Wick-expansion axiom below
is true only for this specific value of `c`; for any other `c`, the
expansion picks up lower-degree terms. -/
noncomputable def gffSiteVariance
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass)
    (x : FinLatticeSites d N) : ℝ :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  (a ^ d)⁻¹ *
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) ^ 2

/-! ## Spectral expansion helper for the site-Wick expansion

The orthogonalized eigenvector coefficient `γ_j(x) = e_j(x) / √(a^d λ_j)`
re-expresses `gffSiteVariance` as `∑ γ_j(x)²` (Parseval-style). This
identity decouples `gffSiteVariance` from the explicit `(a^d)⁻¹` and
`λ_j⁻¹` factors. -/

/-- The orthogonalized eigenvector coefficient: `γ_j(x) = e_j(x) / √(a^d λ_j)`. -/
private noncomputable def gffEigenCoeff
    (a mass : ℝ) (j x : FinLatticeSites d N) : ℝ :=
  (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x /
    Real.sqrt (a^d * massEigenvalues d N a mass j)

/-- Pointwise completeness of the eigenbasis:
`∑ j, e_j(x) · e_j(y) = δ_{xy}`. The (x,y) entry of `M Mᵀ = I` for
the orthonormal basis matrix `M`. -/
private lemma eigenbasis_completeness
    (a mass : ℝ) (x y : FinLatticeSites d N) :
    ∑ j, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x *
        (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) y =
    if y = x then (1 : ℝ) else 0 := by
  -- sum_repr applied to (EuclideanSpace.single x 1):
  -- ∑ j, b.repr (single x 1) j • b j = single x 1.
  have h_repr := (massEigenvectorBasis d N a mass).sum_repr
    (EuclideanSpace.single x (1 : ℝ))
  -- Replace the abstract repr coefficient with e_j(x).
  have h_repr_eq : ∀ j, (massEigenvectorBasis d N a mass).repr
      (EuclideanSpace.single x (1 : ℝ)) j =
      (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x := by
    intro j
    rw [OrthonormalBasis.repr_apply_apply]
    -- ⟨b j, single x 1⟩ via the dotProduct convention used elsewhere:
    -- inner a b = b.ofLp ⬝ᵥ star a.ofLp.
    change ((EuclideanSpace.single x (1 : ℝ)).ofLp ⬝ᵥ
      star (massEigenvectorBasis d N a mass j).ofLp) = _
    simp [dotProduct, star_trivial,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ]
  simp_rw [h_repr_eq] at h_repr
  -- h_repr : ∑ j, e_j(x) • b_j = single x 1 (in EuclideanSpace).
  -- Cast both sides to Pi via ofLp.
  have h_ofLp : ((∑ j, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x •
        (massEigenvectorBasis d N a mass j) : EuclideanSpace ℝ _) :
        FinLatticeSites d N → ℝ) =
      ((EuclideanSpace.single x (1 : ℝ)) : FinLatticeSites d N → ℝ) :=
    congrArg WithLp.ofLp h_repr
  -- Apply at y.
  have h_y := congrFun h_ofLp y
  -- Compute LHS: (∑_j c_j • b_j).ofLp y = ∑_j c_j * b_j.ofLp y.
  -- Convert (∑_j c_j • b_j).ofLp y → ∑_j c_j * (b_j).ofLp y.
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at h_y
  -- Now h_y is `(∑_j c_j • (b_j).ofLp) y = (single x 1).ofLp y`.
  rw [show (∑ j, ((massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x •
        ((massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) :
          FinLatticeSites d N → ℝ))) y =
      ∑ j, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x *
        (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) y from by
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rfl] at h_y
  -- Compute RHS: (single x 1).ofLp y = if y = x then 1 else 0.
  rw [show ((EuclideanSpace.single x (1 : ℝ)) : FinLatticeSites d N → ℝ) y =
      if y = x then (1 : ℝ) else 0 from by rw [EuclideanSpace.single_apply]] at h_y
  exact h_y

/-- Spectral expansion: `ω(δ_x) = ∑_j γ_j(x) · ξ_j(ω)`. -/
private lemma omega_eval_delta_eq_sum_gamma_xi
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (x : FinLatticeSites d N)
    (ω : Configuration (FinLatticeField d N)) :
    ω (Pi.single x (1 : ℝ)) =
    ∑ j, gffEigenCoeff d N a mass j x *
        gffOrthonormalCoord d N a mass ha hmass j ω := by
  -- Step 1: Pi.single x 1 = ∑ j, e_j(x) • (e_j : Pi) (pointwise via eigenbasis_completeness).
  have h_pi_eq : (Pi.single x (1 : ℝ) : FinLatticeField d N) =
      ∑ j, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x •
        ((massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) :
          FinLatticeSites d N → ℝ) := by
    funext y
    rw [show (Pi.single x (1 : ℝ) : FinLatticeField d N) y =
        (if y = x then (1 : ℝ) else 0) from Pi.single_apply _ _ _]
    rw [← eigenbasis_completeness d N a mass x y]
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rfl
  -- Step 2: apply ω-linearity.
  rw [h_pi_eq, map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [map_smul]
  show (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x •
      ω (fun y => (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) y) =
    gffEigenCoeff d N a mass j x *
      gffOrthonormalCoord d N a mass ha hmass j ω
  unfold gffEigenCoeff gffOrthonormalCoord
  simp only [smul_eq_mul]
  have h_pos : (0 : ℝ) < a^d * massEigenvalues d N a mass j :=
    mul_pos (pow_pos ha d)
      (massOperatorMatrix_eigenvalues_pos d N a mass ha hmass j)
  have h_sqrt_ne : Real.sqrt (a^d * massEigenvalues d N a mass j) ≠ 0 :=
    (Real.sqrt_pos.mpr h_pos).ne'
  field_simp

/-- The site variance equals `∑_j γ_j(x)²`. -/
private lemma gffSiteVariance_eq_sum_gamma_sq
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (x : FinLatticeSites d N) :
    gffSiteVariance d N a mass ha hmass x =
    ∑ j, (gffEigenCoeff d N a mass j x)^2 := by
  unfold gffSiteVariance gffEigenCoeff
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have h_pos : (0 : ℝ) < a^d * massEigenvalues d N a mass j :=
    mul_pos (pow_pos ha d)
      (massOperatorMatrix_eigenvalues_pos d N a mass ha hmass j)
  have h_sqrt_sq : Real.sqrt (a^d * massEigenvalues d N a mass j) ^ 2 =
      a^d * massEigenvalues d N a mass j :=
    Real.sq_sqrt h_pos.le
  rw [show ((massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x /
        Real.sqrt (a^d * massEigenvalues d N a mass j))^2 =
      ((massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x)^2 /
        (Real.sqrt (a^d * massEigenvalues d N a mass j))^2 from by
    rw [div_pow]]
  rw [h_sqrt_sq, mul_comm (a^d) (massEigenvalues d N a mass j)]
  field_simp

/-- **Site Wick monomial expansion in the eigenbasis.**

The single-site Wick monomial $\mathopen{:}\phi(x)^k\mathclose{:}_{c_a(x)}$
(with the local Wick constant `c_a(x) = gffSiteVariance d N a mass ha hmass x
= (a^d)⁻¹ Σ_k λ_k⁻¹ e_k(x)²`) admits an explicit linear expansion in
eigenbasis multi-indices:

  `:φ(x)^k:_{c_a(x)} = ∑_{|α| = k} coeff(α, x, k) · :ξ^α:_1`,

where the coefficients are explicit polynomial combinations of the
eigenvector values $e_k(x)$ and eigenvalue powers $\lambda_k^{1/2}$.
The `totalDegree α = k` constraint is the key content: only multi-indices
of *exact* total degree `k` appear, because the local Wick subtraction
with the matched site variance `c_a(x)` cancels exactly the lower-degree
contractions.

**Proof strategy** (deferred): The two helpers above
(`omega_eval_delta_eq_sum_gamma_xi`, `gffSiteVariance_eq_sum_gamma_sq`)
reduce the problem to a generic multivariate Wick multinomial identity:

  for any γ, ξ : ι → ℝ (with ι Fintype) and k : ℕ,
  `wickMonomial k (∑ γ²) (∑ γ_j ξ_j) =
     ∑_{|α|=k} (k!/∏ α_j!) · (∏ γ_j^{α_j}) · ∏_j wickMonomial α_j 1 ξ_j`.

This is the multivariate Hermite multinomial expansion, derivable by
strong induction on k using the 1D Wick recursion + multi-index
combinatorics:

  `:Y^{k+2}:_c = Y · :Y^{k+1}:_c - (k+1) c · :Y^k:_c`
   with `Y = ∑ γ_j ξ_j`, `c = ∑ γ_j²`,
   `Y · :ξ^α:_1 = ∑_j γ_j (:ξ^{α+δ_j}:_1 + α_j · :ξ^{α-δ_j}:_1)`
   (1D Wick recursion per coordinate),
   `c · :ξ^β:_1 = ∑_j γ_j² · :ξ^β:_1`,
   and the algebraic cancellation
   `(β_j+1) · c^{(k+1)}_{β+δ_j} = (k+1) γ_j · c^{(k)}_β`
   for the explicit coefficient `c^{(k)}_α = (k!/∏α_j!) ∏γ_j^{α_j}`.

The induction is rigorous but combinatorially intricate (~300 lines
of multi-index sum manipulation in Lean). Not yet implemented. -/
axiom siteWickMonomial_eigenbasis_expansion
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (x : FinLatticeSites d N) :
    ∃ (coeff : (FinLatticeSites d N → ℕ) → ℝ),
      (∀ α, coeff α ≠ 0 → MultiIndexLattice.totalDegree α = k) ∧
      ∀ ω : Configuration (FinLatticeField d N),
        wickMonomial k (gffSiteVariance d N a mass ha hmass x)
            (ω (Pi.single x 1)) =
        ∑ α ∈ multiIndicesOfDegree d N k, coeff α *
          gffMultiWickMonomial d N a mass ha hmass α ω

end GaussianField
