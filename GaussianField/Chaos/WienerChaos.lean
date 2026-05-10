/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wiener Chaos Decomposition

For the standard Gaussian measure $\gamma$ on $\mathbb R^n$ (we work
in finite dimension; this suffices for `pphi2`'s lattice
applications), the Hilbert space $L^2(\gamma)$ decomposes as an
orthogonal direct sum of homogeneous Wiener chaos:
$$
L^2(\gamma) \;=\; \bigoplus_{k = 0}^{\infty} \mathcal H_k,
$$
where $\mathcal H_k$ is the closure (in $L^2$) of the linear span of
multivariate Hermite polynomials of total degree $k$.

This is the abstract counterpart of the multiple-Wiener-Itô integral
expansion in stochastic calculus, but stated for finite-dimensional
Gaussians where the Hermite definition is purely algebraic and we do
not need any stochastic-integration machinery.

## Main definitions

- `wienerChaos γ k` — the $k$-th chaos as a closed submodule of $L^2(\gamma)$.
- `wienerChaosLE γ d` — `⨆_{k ≤ d} wienerChaos γ k`, the polynomials
  of total degree $\le d$.
- `chaosProjection γ k` — orthogonal projection $L^2(\gamma) \to \mathcal H_k$.

## Main theorems

- `wienerChaos_orthogonal` — distinct chaos spaces are orthogonal in $L^2$.
- `wienerChaos_isHilbertSum` — the chaos spaces form an orthogonal Hilbert
  sum decomposition of $L^2(\gamma)$ (proved from `hermiteMulti_dense`).
- `chaosProjection_mem_wienerChaos`, `chaosProjection_eLpNorm_two_le`,
  `chaosProjection_sum_eq_of_mem_wienerChaosLE`,
  `hermiteMultiEval_mem_wienerChaos` — proved.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), Theorem 2.6.
- D. Nualart, *The Malliavin Calculus and Related Topics*, Springer
  (2006), §1.1.

## Status

`wienerChaos` and `chaosProjection` are now real definitions.
Orthogonality, the chaos sum decomposition for `wienerChaosLE`, and the
full Hilbert-sum decomposition (`wienerChaos_isHilbertSum`) are all
proved from `hermiteMulti_orthogonality` and `hermiteMulti_dense`. The
latter rests on the textbook density axiom
`GaussianField.GeneralResults.polynomial_dense_L2_of_subGaussian`.
-/

import GaussianField.Chaos.HermitePolynomials
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Algebra.DirectSum.Decomposition

noncomputable section

namespace GaussianField.Chaos

open MeasureTheory

variable {n : ℕ}

/-- The set of multivariate Hermite polynomials of total degree $k$,
as functions $(\mathrm{Fin}\ n \to \mathbb R) \to \mathbb R$. -/
def hermiteFamilyOfDegree (n k : ℕ) : Set ((Fin n → ℝ) → ℝ) :=
  { f | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = k ∧ f = hermiteMultiEval α }

/-- `hermiteMultiEval α` is continuous as a function on `Fin n → ℝ`. -/
lemma hermiteMultiEval_continuous {n : ℕ} (α : Fin n → ℕ) :
    Continuous (hermiteMultiEval α) := by
  unfold hermiteMultiEval
  refine continuous_finset_prod _ ?_
  intro i _
  unfold hermiteEval
  exact ((Polynomial.hermite (α i)).map (Int.castRingHom ℝ)).continuous.comp
    (continuous_apply i)

/-- `hermiteMultiEval α` squared is integrable under `γ_n`. -/
lemma hermiteMultiEval_sq_integrable {n : ℕ} (α : Fin n → ℕ) :
    Integrable (fun x => hermiteMultiEval α x ^ 2) (stdGaussianFin n) := by
  -- Use `Integrable.of_integral_ne_zero`: the integral equals `∏ αᵢ!` which is positive.
  apply Integrable.of_integral_ne_zero
  have h_value := hermiteMulti_orthogonality α α
  rw [if_pos rfl] at h_value
  rw [show (fun x => hermiteMultiEval α x ^ 2) =
      (fun x => hermiteMultiEval α x * hermiteMultiEval α x) from by funext x; ring]
  rw [h_value]
  -- ∏ αᵢ! ≥ 1 > 0
  have hpos : (0 : ℝ) < ((∏ i, (α i).factorial : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => Nat.factorial_pos (α i))
  exact ne_of_gt hpos

/-- `hermiteMultiEval α` is in `L²(γ_n)`. -/
lemma hermiteMultiEval_memLp {n : ℕ} (α : Fin n → ℕ) :
    MemLp (hermiteMultiEval α) 2 (stdGaussianFin n) :=
  (memLp_two_iff_integrable_sq
    (hermiteMultiEval_continuous α).aestronglyMeasurable).mpr
    (hermiteMultiEval_sq_integrable α)

/-- Lift `hermiteMultiEval α` to an element of `Lp ℝ 2 (stdGaussianFin n)`. -/
noncomputable def hermiteMultiLp {n : ℕ} (α : Fin n → ℕ) :
    Lp ℝ 2 (stdGaussianFin n) :=
  (hermiteMultiEval_memLp α).toLp _

/-- The `Lp` lift agrees a.e. with the pointwise definition. -/
lemma hermiteMultiLp_coeFn {n : ℕ} (α : Fin n → ℕ) :
    (hermiteMultiLp α : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n] hermiteMultiEval α :=
  MemLp.coeFn_toLp _

/-- The $k$-th Wiener chaos: closed linear span (in $L^2(\gamma)$) of
multivariate Hermite polynomials of total degree $k$.

Concretely, `f ∈ wienerChaos n k` iff `f` is the $L^2$-limit of a
sequence of finite linear combinations of $H_\alpha$ with
$|\alpha| = k$. For $k = 0$ this is the constants; for $k \ge 1$ it is
the centred polynomials of homogeneous degree $k$ modulo lower-degree
Wick subtractions. -/
def wienerChaos (n k : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n)) :=
  (Submodule.span ℝ
    {f | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = k ∧ f = hermiteMultiLp α})
      |>.topologicalClosure

/-- `wienerChaos n k` is closed in `Lp`. -/
lemma wienerChaos_isClosed (n k : ℕ) :
    IsClosed (wienerChaos n k : Set (Lp ℝ 2 (stdGaussianFin n))) :=
  Submodule.isClosed_topologicalClosure _

/-- The carrier of `wienerChaos n k` is a complete metric space. -/
instance wienerChaos_completeSpace (n k : ℕ) :
    CompleteSpace (wienerChaos n k) :=
  (wienerChaos_isClosed n k).isComplete.completeSpace_coe

/-- `wienerChaos n k` always has an orthogonal projection (it's closed
in the complete space `Lp ℝ 2 _`). -/
instance wienerChaos_hasOrthogonalProjection (n k : ℕ) :
    (wienerChaos n k).HasOrthogonalProjection :=
  inferInstance

/-- Polynomials of total degree $\le d$: `⨆_{k ≤ d} wienerChaos γ k`. -/
noncomputable def wienerChaosLE (n d : ℕ) : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n)) :=
  ⨆ k ∈ Finset.range (d + 1), wienerChaos n k

/-- A multivariate Hermite polynomial of total degree $k$ lies in
the $k$-th chaos. (Building block: the chaos contains all of its
Hermite generators.) -/
theorem hermiteMultiLp_mem_wienerChaos (n : ℕ) (α : Fin n → ℕ) :
    hermiteMultiLp α ∈ wienerChaos n (MultiIndex.totalDegree α) :=
  Submodule.le_topologicalClosure _ <| Submodule.subset_span ⟨α, rfl, rfl⟩

/-- A multivariate Hermite polynomial of total degree $k$ lies in
the $k$-th chaos (existential form, matching the legacy axiom signature). -/
theorem hermiteMultiEval_mem_wienerChaos (n : ℕ) (α : Fin n → ℕ)
    (hα : MemLp (hermiteMultiEval α) 2 (stdGaussianFin n)) :
    (hα.toLp _) ∈ wienerChaos n (MultiIndex.totalDegree α) := by
  -- `hα.toLp _ = hermiteMultiLp α` since both are constructed from the same a.e. class.
  have h_eq : hα.toLp _ = hermiteMultiLp α := by
    unfold hermiteMultiLp
    exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.refl _ _)
  rw [h_eq]
  exact hermiteMultiLp_mem_wienerChaos n α

/-- **Orthogonality of `hermiteMultiLp` for distinct total degrees** in `L²(γ)`. -/
theorem hermiteMultiLp_inner_eq_zero_of_totalDegree_ne {n : ℕ} {α β : Fin n → ℕ}
    (hαβ : MultiIndex.totalDegree α ≠ MultiIndex.totalDegree β) :
    @inner ℝ _ _ (hermiteMultiLp α) (hermiteMultiLp β) = 0 := by
  -- The inner product in `Lp ℝ 2 μ` is `∫ a, f a * g a ∂μ` (for ℝ-valued `f, g`).
  rw [L2.inner_def (𝕜 := ℝ)]
  -- The integrand is a.e. equal to the product of the underlying continuous functions.
  have h_aeeq : (fun a => @inner ℝ _ _ ((hermiteMultiLp α : (Fin n → ℝ) → ℝ) a)
                                       ((hermiteMultiLp β : (Fin n → ℝ) → ℝ) a))
              =ᵐ[stdGaussianFin n]
              (fun a => hermiteMultiEval α a * hermiteMultiEval β a) := by
    filter_upwards [hermiteMultiLp_coeFn α, hermiteMultiLp_coeFn β] with a ha hb
    rw [ha, hb]
    -- Now `inner ℝ (h_α a) (h_β a) = h_α a * h_β a`.
    show hermiteMultiEval β a * (starRingEnd ℝ) (hermiteMultiEval α a) = _
    rw [show (starRingEnd ℝ) (hermiteMultiEval α a) = hermiteMultiEval α a from rfl]
    ring
  rw [integral_congr_ae h_aeeq, hermiteMulti_orthogonality]
  have hαβ' : α ≠ β := fun h => hαβ (by rw [h])
  exact if_neg hαβ'

/-- **Orthogonality of distinct chaos spaces.**

For $j \ne k$, `wienerChaos γ j` and `wienerChaos γ k` are orthogonal
subspaces of $L^2(\gamma)$.

**Reference:** Janson Thm 2.6 + multivariate-Hermite orthogonality
(`hermiteMulti_orthogonality`).

**Proof:** The Hermite generators of `wienerChaos n j` and `wienerChaos n k`
are pairwise orthogonal (`hermiteMultiLp_inner_eq_zero_of_totalDegree_ne`),
this extends linearly to spans (`Submodule.isOrtho_span`), then by
continuity of the inner product to the topological closures
(`Submodule.orthogonal_closure`). -/
theorem wienerChaos_orthogonal (n : ℕ) {j k : ℕ} (hjk : j ≠ k)
    (f g : Lp ℝ 2 (stdGaussianFin n))
    (hf : f ∈ wienerChaos n j) (hg : g ∈ wienerChaos n k) :
    @inner ℝ _ _ f g = 0 := by
  -- Strategy: prove `wienerChaos n j ≤ (wienerChaos n k).orthogonal`, then apply.
  -- (1) The Hermite generators of degree j and k are orthogonal.
  -- (2) Hence the spans are orthogonal (`Submodule.isOrtho_span`).
  -- (3) `(wienerChaos n k).orthogonal = (Submodule.span … k).orthogonal` by
  --     `Submodule.orthogonal_closure`.
  -- (4) The closure is the smallest closed submodule containing the span.
  have h_span_le_ortho :
      Submodule.span ℝ
        {h | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = j ∧ h = hermiteMultiLp α}
      ≤ (wienerChaos n k).orthogonal := by
    -- `wienerChaos n k = Sk.topologicalClosure`, and
    -- `(Sk.topologicalClosure).orthogonal = Sk.orthogonal` by `orthogonal_closure`.
    rw [show (wienerChaos n k).orthogonal
        = (Submodule.span ℝ
            {h | ∃ α : Fin n → ℕ, MultiIndex.totalDegree α = k ∧ h = hermiteMultiLp α}).orthogonal
        from Submodule.orthogonal_closure _]
    -- Now `Sj ≤ Sk.orthogonal` is `Sj ⟂ Sk`.
    rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_span]
    rintro u ⟨α, hα_deg, rfl⟩ v ⟨β, hβ_deg, rfl⟩
    apply hermiteMultiLp_inner_eq_zero_of_totalDegree_ne
    rw [hα_deg, hβ_deg]; exact hjk
  have h_closed_le : wienerChaos n j ≤ (wienerChaos n k).orthogonal :=
    Submodule.topologicalClosure_minimal _ h_span_le_ortho
      (Submodule.isClosed_orthogonal _)
  rw [inner_eq_zero_symm]
  exact (h_closed_le hf) g hg

/-- **Wiener chaos decomposition** (Janson Theorem 2.6).

The family `(wienerChaos γ k)_{k ∈ ℕ}` is an orthogonal Hilbert sum
decomposition of $L^2(\gamma)$.

**Proof:**
1. Orthogonality of distinct chaos spaces (`wienerChaos_orthogonal`)
   gives the orthogonal-family hypothesis.
2. Density of polynomials in $L^2(\gamma)$ (`hermiteMulti_dense`)
   gives the totality hypothesis: any `f : Lp ℝ 2 (stdGaussianFin n)`
   is approximated arbitrarily well in `L²` by finite linear
   combinations of multivariate Hermite polynomials, each of which
   lies in some `wienerChaos n (totalDegree α)`. Thus the
   polynomial linear combination belongs to `⨆ k, wienerChaos n k`,
   showing every `f` is in the topological closure of the iSup. -/
theorem wienerChaos_isHilbertSum (n : ℕ) :
    IsHilbertSum ℝ (fun k : ℕ => (wienerChaos n k : Submodule ℝ (Lp ℝ 2 (stdGaussianFin n))))
      (fun k => (wienerChaos n k).subtypeₗᵢ) := by
  refine IsHilbertSum.mkInternal _ ?_ ?_
  · -- OrthogonalFamily
    apply OrthogonalFamily.of_pairwise
    intro j k hjk
    show wienerChaos n j ⟂ wienerChaos n k
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    exact wienerChaos_orthogonal n hjk u v hu hv
  · -- ⊤ ≤ (⨆ k, wienerChaos n k).topologicalClosure
    intro f _
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
    intro ε hε
    -- Apply density of Hermite polynomials with parameter ε².
    have hε_sq : 0 < ε ^ 2 := pow_pos hε 2
    have hf_memLp : MemLp (f : (Fin n → ℝ) → ℝ) 2 (stdGaussianFin n) := Lp.memLp f
    obtain ⟨s, c, hs⟩ :=
      hermiteMulti_dense (f : (Fin n → ℝ) → ℝ) hf_memLp (ε ^ 2) hε_sq
    -- Build the polynomial approximation function.
    set g : (Fin n → ℝ) → ℝ := fun x => ∑ α ∈ s, c α * hermiteMultiEval α x with hg_def
    -- Show g is in L².
    have hg_memLp : MemLp g 2 (stdGaussianFin n) := by
      refine memLp_finset_sum s ?_
      intro α _
      exact (hermiteMultiEval_memLp α).const_mul (c α)
    -- Define the corresponding Lp element.
    set gLp : Lp ℝ 2 (stdGaussianFin n) := hg_memLp.toLp g with hgLp_def
    -- Pointwise: gLp =ᵐ g.
    have h_gLp_ae : (gLp : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n] g :=
      MemLp.coeFn_toLp hg_memLp
    -- Inline lemma: the coercion of a finite Lp sum is a.e. the sum of the coercions.
    have h_coeFn_sum : ∀ (t : Finset (Fin n → ℕ))
        (F : (Fin n → ℕ) → Lp ℝ 2 (stdGaussianFin n)),
        ((∑ i ∈ t, F i : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
          =ᵐ[stdGaussianFin n] ∑ i ∈ t, ((F i : Lp ℝ 2 (stdGaussianFin n))
            : (Fin n → ℝ) → ℝ) := by
      intro t F
      classical
      induction t using Finset.induction with
      | empty =>
          simp only [Finset.sum_empty]
          exact Lp.coeFn_zero ℝ 2 (stdGaussianFin n)
      | insert i t hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi]
          filter_upwards [Lp.coeFn_add (F i) (∑ j ∈ t, F j), ih]
            with x hx_add hx_ih
          simp only [Pi.add_apply, Finset.sum_apply] at hx_add hx_ih ⊢
          rw [hx_add, hx_ih]
    refine ⟨gLp, ?_, ?_⟩
    · -- gLp ∈ ⨆ k, wienerChaos n k
      -- Show gLp = ∑ α ∈ s, c α • hermiteMultiLp α as Lp elements.
      have h_sum_eq : gLp = ∑ α ∈ s, c α • hermiteMultiLp α := by
        apply Lp.ext
        -- Goal: ⇑gLp =ᵐ[μ] ⇑(∑ α ∈ s, c α • hermiteMultiLp α)
        refine h_gLp_ae.trans ?_
        -- Goal: g =ᵐ[μ] ⇑(∑ α ∈ s, c α • hermiteMultiLp α)
        symm
        -- Goal: ⇑(∑ α ∈ s, c α • hermiteMultiLp α) =ᵐ[μ] g
        have h_sum_coe := h_coeFn_sum s (fun α => c α • hermiteMultiLp α)
        refine h_sum_coe.trans ?_
        -- Goal: ∑ α ∈ s, ⇑(c α • hermiteMultiLp α) =ᵐ[μ] g
        have h_each : ∀ α ∈ (s : Set (Fin n → ℕ)),
            ∀ᵐ x ∂(stdGaussianFin n),
              ((c α • hermiteMultiLp α : Lp ℝ 2 (stdGaussianFin n))
                  : (Fin n → ℝ) → ℝ) x = c α * hermiteMultiEval α x := by
          intro α _
          have h1 : ((c α • hermiteMultiLp α : Lp ℝ 2 (stdGaussianFin n))
                : (Fin n → ℝ) → ℝ) =ᵐ[stdGaussianFin n]
                fun x => c α * hermiteMultiEval α x := by
            refine (Lp.coeFn_smul (c α) (hermiteMultiLp α)).trans ?_
            filter_upwards [hermiteMultiLp_coeFn α] with x hx
            simp [hx, smul_eq_mul]
          exact h1
        have h_ae_all : ∀ᵐ x ∂(stdGaussianFin n), ∀ α ∈ (s : Set (Fin n → ℕ)),
            ((c α • hermiteMultiLp α : Lp ℝ 2 (stdGaussianFin n))
                : (Fin n → ℝ) → ℝ) x = c α * hermiteMultiEval α x :=
          (ae_ball_iff s.countable_toSet).mpr h_each
        filter_upwards [h_ae_all] with x hx
        show (∑ α ∈ s, ((c α • hermiteMultiLp α : Lp ℝ 2 (stdGaussianFin n))
              : (Fin n → ℝ) → ℝ)) x = g x
        rw [Finset.sum_apply]
        exact Finset.sum_congr rfl (fun α hα => hx α (Finset.mem_coe.mpr hα))
      rw [h_sum_eq]
      -- Each c α • hermiteMultiLp α ∈ wienerChaos n (totalDegree α) ≤ ⨆ k, wienerChaos n k.
      apply Submodule.sum_mem
      intro α _
      apply Submodule.smul_mem
      have h_mem : hermiteMultiLp α ∈ wienerChaos n (MultiIndex.totalDegree α) :=
        hermiteMultiLp_mem_wienerChaos n α
      exact (le_iSup (fun k : ℕ => wienerChaos n k) (MultiIndex.totalDegree α)) h_mem
    · -- dist f gLp < ε.
      -- Strategy: ‖f - gLp‖² = ⟨f - gLp, f - gLp⟩_ℝ = ∫ (f - gLp)² < ε².
      have h_diff_ae :
          ((f - gLp : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ)
            =ᵐ[stdGaussianFin n] fun x => (f : (Fin n → ℝ) → ℝ) x - g x := by
        refine (Lp.coeFn_sub f gLp).trans ?_
        filter_upwards [h_gLp_ae] with x hx
        simp [hx]
      -- ‖f - gLp‖² = ∫ ((f - gLp) x)^2 ∂μ
      have h_norm_sq :
          ‖f - gLp‖ ^ 2
            = ∫ x, ((f : (Fin n → ℝ) → ℝ) x - g x) ^ 2 ∂(stdGaussianFin n) := by
        rw [← @real_inner_self_eq_norm_sq _ _ _ (f - gLp), L2.inner_def (𝕜 := ℝ)]
        refine integral_congr_ae ?_
        filter_upwards [h_diff_ae] with x hx
        show ((f - gLp : Lp ℝ 2 (stdGaussianFin n)) : (Fin n → ℝ) → ℝ) x *
              (starRingEnd ℝ) (((f - gLp : Lp ℝ 2 (stdGaussianFin n)) :
                (Fin n → ℝ) → ℝ) x) = _
        rw [hx]
        simp [sq]
      have h_norm_sq_lt : ‖f - gLp‖ ^ 2 < ε ^ 2 := by
        rw [h_norm_sq]
        -- ∫ ((f - gLp) x)^2 ∂μ < ε^2; from hs we have integral with abs.
        have h_eq : ∀ x,
            ((f : (Fin n → ℝ) → ℝ) x - g x) ^ 2
              = |(f : (Fin n → ℝ) → ℝ) x - g x| ^ 2 := by
          intro x
          rw [sq_abs]
        simp only [h_eq]
        exact hs
      -- dist f gLp = ‖f - gLp‖.
      rw [dist_eq_norm]
      have h_norm_nonneg : 0 ≤ ‖f - gLp‖ := norm_nonneg _
      exact lt_of_pow_lt_pow_left₀ 2 hε.le h_norm_sq_lt

/-- **Orthogonal projection onto the $k$-th chaos.** -/
noncomputable def chaosProjection (n k : ℕ) :
    Lp ℝ 2 (stdGaussianFin n) →L[ℝ] Lp ℝ 2 (stdGaussianFin n) :=
  (wienerChaos n k).starProjection

/-- **Range of the chaos projection:** `chaosProjection n k F ∈ wienerChaos n k`. -/
theorem chaosProjection_mem_wienerChaos (n k : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n)) :
    chaosProjection n k F ∈ wienerChaos n k :=
  Submodule.starProjection_apply_mem _ _

/-- **Chaos projection is `L²`-contractive:** `‖P_k F‖₂ ≤ ‖F‖₂`. -/
theorem chaosProjection_eLpNorm_two_le (n k : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n)) :
    eLpNorm ((chaosProjection n k F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) ≤
      eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) := by
  -- Convert eLpNorm of the coercion to enorm of the Lp element.
  have h₁ : eLpNorm ((chaosProjection n k F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n)
      = ‖chaosProjection n k F‖ₑ := (Lp.enorm_def _).symm
  have h₂ : eLpNorm ((F : (Fin n → ℝ) → ℝ)) 2 (stdGaussianFin n) = ‖F‖ₑ :=
    (Lp.enorm_def _).symm
  rw [h₁, h₂, enorm_le_iff_norm_le]
  exact Submodule.norm_starProjection_apply_le _ _

/-- **Chaos decomposition for elements of `wienerChaosLE n d`:**
$F \;=\; \sum_{k = 0}^{d} P_k F$, where $P_k = $ `chaosProjection n k`.

This follows from Mathlib's `OrthogonalFamily.sum_projection_of_mem_iSup`
applied to the family `(wienerChaos n k)_{k ∈ Fin (d+1)}`, which is
orthogonal by `wienerChaos_orthogonal` and whose `iSup` equals
`wienerChaosLE n d`. -/
theorem chaosProjection_sum_eq_of_mem_wienerChaosLE (n d : ℕ)
    (F : Lp ℝ 2 (stdGaussianFin n)) (hF : F ∈ wienerChaosLE n d) :
    F = ∑ k ∈ Finset.range (d + 1), chaosProjection n k F := by
  classical
  -- Reindex over `Fin (d+1)` so we can use `OrthogonalFamily.sum_projection_of_mem_iSup`.
  let V : Fin (d + 1) → Submodule ℝ (Lp ℝ 2 (stdGaussianFin n)) :=
    fun k => wienerChaos n k.val
  have hV_ortho : OrthogonalFamily ℝ (fun i => V i)
      (fun i => (V i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    show V i ⟂ V j
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    refine wienerChaos_orthogonal n ?_ u v hu hv
    intro h
    exact hij (Fin.ext h)
  -- Reformulate the membership: `F ∈ wienerChaosLE n d = ⨆_{k ≤ d} wienerChaos n k = ⨆ i : Fin (d+1), V i`.
  have h_eq_sup : (⨆ i : Fin (d + 1), V i) = wienerChaosLE n d := by
    unfold wienerChaosLE
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      refine le_iSup_of_le (i : ℕ) ?_
      exact le_iSup (fun (_ : (i : ℕ) ∈ Finset.range (d + 1)) => wienerChaos n (i : ℕ))
        (Finset.mem_range.mpr i.isLt)
    · refine iSup_le ?_
      intro k
      refine iSup_le ?_
      intro hk
      have hk' : k < d + 1 := Finset.mem_range.mp hk
      exact le_iSup V (⟨k, hk'⟩ : Fin (d + 1))
  have hF' : F ∈ ⨆ i : Fin (d + 1), V i := by rw [h_eq_sup]; exact hF
  -- Apply the projection-sum theorem from the orthogonal family.
  have h_sum := hV_ortho.sum_projection_of_mem_iSup F hF'
  -- Convert the Fin-sum back to a `Finset.range (d+1)` sum.
  have h_each : ∀ i : Fin (d + 1), (V i).starProjection F = chaosProjection n (i : ℕ) F :=
    fun _ => rfl
  calc F = ∑ i : Fin (d + 1), (V i).starProjection F := h_sum.symm
    _ = ∑ i : Fin (d + 1), chaosProjection n (i : ℕ) F :=
        Finset.sum_congr rfl (fun i _ => h_each i)
    _ = ∑ k ∈ Finset.range (d + 1), chaosProjection n k F := by
        rw [← Finset.sum_range (fun k => chaosProjection n k F)]

end GaussianField.Chaos
