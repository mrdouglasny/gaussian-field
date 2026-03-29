/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Separately Continuous Multilinear Maps are Jointly Continuous

Proves that separately continuous multilinear maps on Baire topological
vector spaces (valued in the scalar field) are jointly continuous.

This eliminates the axiom `exists_continuousMultilinear_ofSeparatelyContinuous`
in OSreconstruction/Wightman/WightmanAxioms.lean.

## Main result

- `exists_continuousMultilinear_ofSeparatelyContinuous` — separately continuous
  n-linear map on a first-countable Baire TVS is jointly continuous

## References

- Bourbaki, "Topological Vector Spaces", III.3.5
- Rudin, "Functional Analysis", Theorem 2.17
-/

import GaussianField.Tightness
import Mathlib.Topology.Algebra.Module.Multilinear.Topology

noncomputable section

open GaussianField Filter Topology

namespace GaussianField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

/-! ## Main theorem -/

/-- A separately continuous multilinear map on a first-countable Baire space
valued in the scalar field is jointly continuous.

**Proof**: Induction on `n`. The `n = 0` case is trivial.
For `n + 1`, decompose `Φ(m) = Φ.curryLeft(m 0)(tail m)` via linearity into
an error term (linear in `m 0 - m₀ 0`) and a main term (continuous by IH).
The error term vanishes by a Banach-Steinhaus argument: by contradiction,
extract sequences `hₖ → 0`, `gsₖ → gs₀` violating the bound. The family
of CLFs `{h ↦ Φ.curryLeft h gsₖ}` is pointwise bounded (convergent → bounded),
so `Seminorm.continuous_iSup` (Baire → barrelled → iSup of continuous
seminorms is continuous) gives a uniform bound, contradicting the extraction. -/
theorem multilinear_continuous_of_separatelyContinuous
    [BaireSpace E] [FirstCountableTopology E]
    {n : ℕ}
    (Phi : MultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜)
    (hPhi : ∀ (i : Fin n) (fs : Fin n → E),
      Continuous (fun f => Phi (Function.update fs i f))) :
    Continuous Phi := by
  induction n with
  | zero =>
    have heq : ∀ fs : Fin 0 → E, fs = Fin.elim0 := by
      intro fs; ext i; exact Fin.elim0 i
    have hconst : ∀ fs : Fin 0 → E, Phi fs = Phi Fin.elim0 := by
      intro fs; congr 1; exact heq fs
    show Continuous (fun fs => Phi fs)
    simp_rw [hconst]; exact continuous_const
  | succ n ih =>
    -- Step 1: curryLeft x₀ is separately continuous, hence continuous by IH.
    have hcurry_sep : ∀ (x₀ : E) (j : Fin n) (gs : Fin n → E),
        Continuous (fun g => Phi.curryLeft x₀ (Function.update gs j g)) := by
      intro x₀ j gs
      have key : ∀ g : E, Phi.curryLeft x₀ (Function.update gs j g) =
          Phi (Function.update (Fin.cons x₀ gs) j.succ g) := by
        intro g; simp only [MultilinearMap.curryLeft_apply, Fin.cons_update]
      simp_rw [key]; exact hPhi j.succ (Fin.cons x₀ gs)
    have hcurry_cont : ∀ x₀ : E, Continuous (Phi.curryLeft x₀) :=
      fun x₀ => ih (Phi.curryLeft x₀) (hcurry_sep x₀)
    -- h ↦ Phi.curryLeft h gs is continuous for each gs (separate continuity in slot 0).
    have hcont_h : ∀ gs : Fin n → E,
        Continuous (fun h : E => Phi.curryLeft h gs) := by
      intro gs
      have : (fun h => Phi.curryLeft h gs) =
          (fun h => Phi (Function.update (Fin.cons 0 gs) 0 h)) := by
        ext h; simp [MultilinearMap.curryLeft_apply]
      rw [this]; exact hPhi 0 (Fin.cons 0 gs)
    -- Step 2: Show ContinuousAt at each point.
    apply continuous_iff_continuousAt.mpr
    intro fs₀
    have hPhi_eq : ∀ m : Fin (n + 1) → E,
        Phi m = (Phi.curryLeft (m 0)) (Fin.tail m) := by
      intro m; simp [MultilinearMap.curryLeft_apply, Fin.cons_self_tail]
    rw [ContinuousAt]
    show Tendsto (fun fs => Phi fs) (nhds fs₀) (nhds (Phi fs₀))
    have hPhi_eq' : (fun fs => Phi fs) = (fun fs =>
        Phi.curryLeft (fs 0) (Fin.tail fs)) := by ext fs; exact hPhi_eq fs
    rw [hPhi_eq']
    -- Decompose: Phi.curryLeft(fs 0)(tail fs) = error + main
    have hdecomp : ∀ fs : Fin (n + 1) → E,
        Phi.curryLeft (fs 0) (Fin.tail fs) =
        Phi.curryLeft (fs 0 - fs₀ 0) (Fin.tail fs) + Phi.curryLeft (fs₀ 0) (Fin.tail fs) := by
      intro fs
      have : Phi.curryLeft (fs 0) = Phi.curryLeft (fs 0 - fs₀ 0) + Phi.curryLeft (fs₀ 0) := by
        rw [← Phi.curryLeft.map_add, sub_add_cancel]
      rw [this]; rfl
    simp_rw [hdecomp]
    rw [← zero_add (Phi fs₀)]
    apply Tendsto.add
    · -- ERROR TERM: Phi.curryLeft (fs 0 - fs₀ 0) (tail fs) → 0
      -- By contradiction + Banach-Steinhaus (Seminorm.continuous_iSup).
      set gs₀ := Fin.tail fs₀
      rw [tendsto_def]
      intro U hU
      rw [Metric.mem_nhds_iff] at hU
      obtain ⟨ε, hε_pos, hε_sub⟩ := hU
      -- Suffices: ∃ᶠ fs, ‖Phi.curryLeft (fs 0 - fs₀ 0) (tail fs)‖ < ε
      suffices ∃ V ∈ nhds fs₀, ∀ fs ∈ V, ‖Phi.curryLeft (fs 0 - fs₀ 0) (Fin.tail fs)‖ < ε by
        obtain ⟨V, hV, hVε⟩ := this
        exact Filter.mem_of_superset hV (fun fs hfs =>
          hε_sub (Metric.mem_ball.mpr (by rw [dist_zero_right]; exact hVε fs hfs)))
      -- by_contra: extract sequences h_k → 0, gs_k → gs₀ violating the bound.
      by_contra hH
      push_neg at hH
      -- hH : ∀ V ∈ nhds fs₀, ∃ fs ∈ V, ε ≤ ‖Phi.curryLeft (fs 0 - fs₀ 0) (tail fs)‖
      obtain ⟨V_basis, hV_basis⟩ := (nhds fs₀).exists_antitone_basis
      choose fs_seq hfs_mem hfs_bound using fun k => hH (V_basis k) (hV_basis.mem k)
      have hfs_lim : Tendsto fs_seq atTop (nhds fs₀) := hV_basis.tendsto hfs_mem
      -- h_k = fs_seq k 0 - fs₀ 0 → 0:
      have hh_lim : Tendsto (fun k => fs_seq k 0 - fs₀ 0) atTop (nhds 0) := by
        have h1 : Tendsto (fun k => fs_seq k 0) atTop (nhds (fs₀ 0)) :=
          (continuous_apply (0 : Fin (n + 1))).continuousAt.tendsto.comp hfs_lim
        have h2 : Tendsto (fun k => fs_seq k 0 - fs₀ 0) atTop (nhds (fs₀ 0 - fs₀ 0)) :=
          h1.sub tendsto_const_nhds
        rwa [sub_self] at h2
      -- gs_k = tail (fs_seq k) → gs₀:
      have hgs_lim : Tendsto (fun k => Fin.tail (fs_seq k)) atTop (nhds gs₀) :=
        (continuous_pi (fun i => continuous_apply (Fin.succ i))).continuousAt.tendsto.comp hfs_lim
      -- Define CLFs: φ_k(h) = Phi.curryLeft h (tail (fs_seq k))
      set φ : ℕ → E →L[𝕜] 𝕜 := fun k =>
        { toLinearMap :=
            { toFun := fun h => Phi.curryLeft h (Fin.tail (fs_seq k))
              map_add' := by intro x y; simp [map_add, MultilinearMap.add_apply]
              map_smul' := by intro c x; simp [map_smul, MultilinearMap.smul_apply] }
          cont := hcont_h (Fin.tail (fs_seq k)) }
      -- Seminorms: p_k(h) = ‖φ_k(h)‖
      set p : ℕ → Seminorm 𝕜 E := fun k => (normSeminorm 𝕜 𝕜).comp (φ k).toLinearMap
      -- Each p_k is continuous:
      have hp_cont : ∀ k, Continuous (p k) := fun k => (φ k).continuous.norm
      -- Pointwise bounded: for each h, φ_k(h) → Phi.curryLeft h gs₀ (by hcurry_cont):
      have hp_bdd : BddAbove (Set.range p) := by
        rw [Seminorm.bddAbove_range_iff]
        intro h
        have hconv : Tendsto (fun k => (φ k) h) atTop (nhds (Phi.curryLeft h gs₀)) :=
          (hcurry_cont h).continuousAt.tendsto.comp hgs_lim
        have hconv_norm : Tendsto (fun k => ‖(φ k) h‖) atTop (nhds ‖Phi.curryLeft h gs₀‖) :=
          hconv.norm
        exact hconv_norm.bddAbove_range
      -- Banach-Steinhaus: iSup of p_k is continuous (on barrelled space).
      haveI : BarrelledSpace 𝕜 E := BaireSpace.instBarrelledSpace
      have hp_sup_cont : Continuous (⨆ k, p k) := Seminorm.continuous_iSup p hp_cont hp_bdd
      -- Use the Seminorm iSup consistently.
      set pSup : Seminorm 𝕜 E := ⨆ k, p k with pSup_def
      -- (⨆ p_k)(0) = 0:
      have hp_sup_zero : pSup (0 : E) = 0 := map_zero _
      -- Continuity of the seminorm iSup as a function:
      have hp_sup_cont' : Continuous pSup := by
        have : (pSup : E → ℝ) = ⨆ k, ⇑(p k) := by
          rw [pSup_def]; exact Seminorm.coe_iSup_eq hp_bdd
        rw [show (⇑pSup : E → ℝ) = (pSup : E → ℝ) from rfl, this]; exact hp_sup_cont
      -- By continuity at 0: ∃ V₀ ∈ nhds 0, pSup(h) < ε for h ∈ V₀.
      have hV₀ : ⇑pSup ⁻¹' Metric.ball 0 ε ∈ nhds (0 : E) :=
        hp_sup_cont'.continuousAt.preimage_mem_nhds
          (by rw [hp_sup_zero]; exact Metric.ball_mem_nhds 0 hε_pos)
      -- h_k = fs_seq k 0 - fs₀ 0 → 0, so eventually h_k ∈ preimage.
      have hh_inV : ∀ᶠ k in atTop, fs_seq k 0 - fs₀ 0 ∈ pSup ⁻¹' Metric.ball 0 ε :=
        hh_lim hV₀
      -- For such k: pSup(h_k) < ε, hence p_k(h_k) ≤ pSup(h_k) < ε.
      -- i.e., ‖Phi.curryLeft h_k (tail (fs_seq k))‖ < ε.
      -- But hfs_bound says: ε ≤ ‖Phi.curryLeft h_k (tail (fs_seq k))‖.
      -- Contradiction!
      obtain ⟨k₀, hk₀⟩ := hh_inV.exists
      have hle : p k₀ (fs_seq k₀ 0 - fs₀ 0) ≤ pSup (fs_seq k₀ 0 - fs₀ 0) := by
        have h_le_sem : p k₀ ≤ pSup := pSup_def ▸ le_ciSup hp_bdd k₀
        exact h_le_sem _
      have hlt : pSup (fs_seq k₀ 0 - fs₀ 0) < ε := by
        simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] at hk₀
        rwa [abs_of_nonneg (apply_nonneg pSup _)] at hk₀
      have hpk_eq : p k₀ (fs_seq k₀ 0 - fs₀ 0) =
          ‖Phi.curryLeft (fs_seq k₀ 0 - fs₀ 0) (Fin.tail (fs_seq k₀))‖ := by
        simp only [p, φ, Seminorm.comp_apply, coe_normSeminorm,
          LinearMap.coe_mk, AddHom.coe_mk]
      linarith [hfs_bound k₀]
    · -- MAIN TERM: Phi.curryLeft (fs₀ 0) (tail fs) → Phi(fs₀)
      rw [hPhi_eq fs₀]
      exact (hcurry_cont (fs₀ 0)).continuousAt.comp
        (continuous_pi (fun i => continuous_apply (Fin.succ i))).continuousAt

/-- **Separately continuous multilinear maps on first-countable Baire spaces
are jointly continuous.**

Every separately continuous multilinear map `Φ : Eⁿ → 𝕜` on a first-countable
Baire topological vector space over a nontrivially normed field is jointly
continuous, and hence lifts to a `ContinuousMultilinearMap`.

The first-countability hypothesis is satisfied by all Fréchet spaces,
Schwartz spaces, and DyninMityaginSpaces (metrizable via countable seminorms). -/
theorem exists_continuousMultilinear_ofSeparatelyContinuous
    [BaireSpace E] [FirstCountableTopology E]
    {n : ℕ}
    (Phi : MultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜)
    (hPhi : ∀ (i : Fin n) (fs : Fin n → E),
      Continuous (fun f => Phi (Function.update fs i f))) :
    ∃ PhiCont : ContinuousMultilinearMap 𝕜 (fun _ : Fin n => E) 𝕜,
      ∀ fs : Fin n → E, PhiCont fs = Phi fs :=
  ⟨{ Phi with cont := multilinear_continuous_of_separatelyContinuous Phi hPhi }, fun _ => rfl⟩

end GaussianField
