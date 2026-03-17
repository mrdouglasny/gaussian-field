import GeneralResults.SchwartzProducts
import SchwartzNuclear.NuclearExtension
import Mathlib.Analysis.Complex.Basic

noncomputable section
open GaussianField Finset
set_option maxHeartbeats 6400000

namespace GaussianField

private def myBlockMI (n d : ℕ) (α : Fin (n * d) → ℕ) (i : Fin n) : Fin d → ℕ :=
  fun j => α (finProdFinEquiv (i, j))

private lemma myBlockMI_abs_le (n d : ℕ) (α : Fin (n * d) → ℕ) (i : Fin n) :
    MultiIndex.abs (myBlockMI n d α i) ≤ MultiIndex.abs α := by
  simp only [MultiIndex.abs, myBlockMI]
  calc ∑ j : Fin d, α (finProdFinEquiv (i, j))
      = ∑ J ∈ univ.image (fun j : Fin d => finProdFinEquiv (i, j)), α J := by
        rw [Finset.sum_image]; intro a _ b _ hab
        exact congrArg Prod.snd (finProdFinEquiv.injective hab)
    _ ≤ ∑ J : Fin (n * d), α J :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun _ _ => mem_univ _) (fun _ _ _ => Nat.zero_le _)

-- Helper: Fin-cast preserves MultiIndex.abs (generalize + rcases approach)
private lemma abs_cast_general (d : ℕ) (hd : 0 < d) (f : Fin d → ℕ) :
    MultiIndex.abs (Nat.succ_pred_eq_of_pos hd ▸ f : Fin (d - 1 + 1) → ℕ) =
    MultiIndex.abs f := by
  generalize d = d₀ at *; rcases d₀ with _ | d'; · omega; · rfl

-- Helper: Fin-cast preserves MultiIndex.abs for the α cast
private lemma abs_cast_general' (N : ℕ) (hN : 0 < N)
    (α₀ : Fin (N - 1 + 1) → ℕ) :
    MultiIndex.abs (Nat.succ_pred_eq_of_pos hN ▸ α₀ : Fin N → ℕ) =
    MultiIndex.abs α₀ := by
  generalize N = N₀ at *; rcases N₀ with _ | N'; · omega; · rfl

lemma productBasisIndices_polyGrowth
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [Nontrivial D]
    (n : ℕ) (hn : 0 < n) :
    ∃ D_enc > 0, ∃ q : ℕ, ∀ m i,
      (productBasisIndices (D := D) n hn m i : ℝ) ≤ D_enc * (1 + (m : ℝ)) ^ q := by
  have hd : 0 < Module.finrank ℝ D := Module.finrank_pos
  have hnd : 0 < n * Module.finrank ℝ D := Nat.mul_pos hn hd
  obtain ⟨C₁, hC₁, k₁, h_symm⟩ := multiIndexEquiv_symm_growth (n * Module.finrank ℝ D - 1)
  obtain ⟨C₂, hC₂, k₂, h_growth⟩ := multiIndexEquiv_growth (Module.finrank ℝ D - 1)
  refine ⟨C₂ * C₁ ^ k₂, by positivity, k₁ * k₂, fun m i => ?_⟩
  -- Unfold pbi via definitional equality with myBlockMI
  have hpbi_eq : productBasisIndices (D := D) n hn m i =
    (multiIndexEquiv (Module.finrank ℝ D - 1))
      (Nat.succ_pred_eq_of_pos hd ▸
        myBlockMI n (Module.finrank ℝ D)
          (Nat.succ_pred_eq_of_pos hnd ▸
            (multiIndexEquiv (n * Module.finrank ℝ D - 1)).symm m) i) := by
    simp only [productBasisIndices]; rfl
  rw [hpbi_eq]
  -- Set up names
  set α₀ := (multiIndexEquiv (n * Module.finrank ℝ D - 1)).symm m
  set α := (Nat.succ_pred_eq_of_pos hnd ▸ α₀ : Fin (n * Module.finrank ℝ D) → ℕ)
  set block := myBlockMI n (Module.finrank ℝ D) α i
  set β := (Nat.succ_pred_eq_of_pos hd ▸ block : Fin (Module.finrank ℝ D - 1 + 1) → ℕ)
  -- Step 1: 1 + (multiIndexEquiv ...) β ≤ C₂ * (1 + |β|)^k₂
  have h1 := h_growth β
  -- Step 2: |β| = |block| (cast preserves abs)
  have h_abs_β : MultiIndex.abs β = MultiIndex.abs block :=
    abs_cast_general (Module.finrank ℝ D) hd block
  -- Step 3: |block| ≤ |α| (block is a sub-sum)
  have h_abs_block : MultiIndex.abs block ≤ MultiIndex.abs α :=
    myBlockMI_abs_le n (Module.finrank ℝ D) α i
  -- Step 4: |α| = |α₀| (cast preserves abs)
  have h_abs_α : MultiIndex.abs α = MultiIndex.abs α₀ :=
    abs_cast_general' (n * Module.finrank ℝ D) hnd α₀
  -- Step 5: 1 + |α₀| ≤ C₁ * (1+m)^k₁
  have h3 := h_symm m
  -- Chain: |β| ≤ |α₀|, hence 1 + |β| ≤ C₁ * (1+m)^k₁
  have h_chain : (MultiIndex.abs β : ℝ) ≤ C₁ * (1 + (m : ℝ)) ^ k₁ - 1 := by
    have : MultiIndex.abs β ≤ MultiIndex.abs α₀ :=
      h_abs_β ▸ h_abs_α ▸ h_abs_block
    linarith [show (MultiIndex.abs β : ℝ) ≤ (MultiIndex.abs α₀ : ℝ) from by exact_mod_cast this]
  -- Final bound
  calc ((multiIndexEquiv (Module.finrank ℝ D - 1)) β : ℝ)
      ≤ C₂ * (1 + (MultiIndex.abs β : ℝ)) ^ k₂ - 1 := by linarith [h1]
    _ ≤ C₂ * (C₁ * (1 + (m : ℝ)) ^ k₁) ^ k₂ - 1 := by
        gcongr
        exact pow_le_pow_left₀ (by positivity) (by linarith [h_chain]) k₂
    _ = C₂ * C₁ ^ k₂ * (1 + (m : ℝ)) ^ (k₁ * k₂) - 1 := by rw [mul_pow]; ring_nf
    _ ≤ C₂ * C₁ ^ k₂ * (1 + (m : ℝ)) ^ (k₁ * k₂) := by linarith

end GaussianField
