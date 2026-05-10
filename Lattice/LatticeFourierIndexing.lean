import Lattice.CirculantDFT2d

noncomputable section

namespace GaussianField

open scoped BigOperators
open Real

variable (N : ℕ) [NeZero N]

/-- Reindex a sum over `ZMod N` as a sum over `Fin N` via `ZMod.val`. -/
private lemma zmod_sum_eq_fin_sum {α : Type*} [AddCommMonoid α] (g : ℕ → α) :
    ∑ x : ZMod N, g (ZMod.val x) =
    ∑ n : Fin N, g n.val := by
  exact Fintype.sum_bijective
    (fun (x : ZMod N) =>
      (⟨ZMod.val x, ZMod.val_lt x⟩ : Fin N))
    ⟨fun a b h => ZMod.val_injective N (Fin.mk.inj h),
     fun ⟨n, hn⟩ =>
      ⟨(n : ZMod N), by
        ext
        exact ZMod.val_natCast_of_lt hn⟩⟩
    _ _ (fun _ => rfl)

/-- Raw torus frequency corresponding to the real Fourier mode ordering
`0, cos(1), sin(1), cos(2), sin(2), ...`. -/
private noncomputable def realModeToRaw (m : Fin N) : Fin N :=
  match m with
  | ⟨0, _⟩ => 0
  | ⟨n + 1, hm⟩ =>
      let k := n / 2 + 1
      if hn_even : n % 2 = 0 then
        ⟨k, by omega⟩
      else
        ⟨N - k, by omega⟩

private lemma realModeToRaw_succ_even (n : ℕ) (hm : n + 1 < N)
    (hn_even : n % 2 = 0) :
    realModeToRaw (N := N) (⟨n + 1, hm⟩ : Fin N) =
      ⟨n / 2 + 1, by omega⟩ := by
  simp [realModeToRaw, hn_even]

private lemma realModeToRaw_succ_odd (n : ℕ) (hm : n + 1 < N)
    (hn_odd : n % 2 ≠ 0) :
    realModeToRaw (N := N) (⟨n + 1, hm⟩ : Fin N) =
      ⟨N - (n / 2 + 1), by omega⟩ := by
  simp [realModeToRaw, hn_odd]

/-- Inverse of `realModeToRaw`. -/
private noncomputable def rawModeToReal (k : Fin N) : Fin N :=
  if hk0 : k.val = 0 then
    0
  else if hk_small : 2 * k.val ≤ N then
    ⟨2 * k.val - 1, by omega⟩
  else
    ⟨2 * (N - k.val), by omega⟩

private lemma rawModeToReal_realModeToRaw (m : Fin N) :
    rawModeToReal (N := N) (realModeToRaw (N := N) m) = m := by
  rcases m with ⟨_|n, hm⟩
  · simp [realModeToRaw, rawModeToReal]
  · set k : ℕ := n / 2 + 1
    by_cases hn_even : n % 2 = 0
    · have hk0 : k ≠ 0 := by omega
      have hk_small : 2 * k ≤ N := by omega
      rw [show realModeToRaw (N := N) ⟨n + 1, hm⟩ = ⟨k, by omega⟩ by
        simp [realModeToRaw, k, hn_even]]
      rw [show rawModeToReal (N := N) (⟨k, by omega⟩ : Fin N) = ⟨2 * k - 1, by omega⟩ by
        simp [rawModeToReal, hk0, hk_small]]
      have hk_eq : 2 * k - 1 = n + 1 := by
        unfold k
        omega
      exact Fin.ext hk_eq
    · have hk0 : N - k ≠ 0 := by omega
      have hk_not_small : ¬ 2 * (N - k) ≤ N := by omega
      rw [show realModeToRaw (N := N) ⟨n + 1, hm⟩ = ⟨N - k, by omega⟩ by
        simp [realModeToRaw, k, hn_even]]
      rw [show rawModeToReal (N := N) (⟨N - k, by omega⟩ : Fin N) =
          ⟨2 * (N - (N - k)), by omega⟩ by
        simp [rawModeToReal, hk0, hk_not_small]]
      have hk_eq : 2 * (N - (N - k)) = n + 1 := by
        unfold k
        omega
      exact Fin.ext hk_eq

private lemma realModeToRaw_rawModeToReal (k : Fin N) :
    realModeToRaw (N := N) (rawModeToReal (N := N) k) = k := by
  rcases k with ⟨k, hk⟩
  by_cases hk0 : k = 0
  · subst hk0
    change (0 : Fin N) = 0
    rfl
  · by_cases hk_small : 2 * k ≤ N
    · have hk0' : k ≠ 0 := hk0
      have hn_even : (2 * k - 2) % 2 = 0 := by omega
      rw [show rawModeToReal (N := N) ⟨k, hk⟩ = ⟨2 * k - 1, by omega⟩ by
        simp [rawModeToReal, hk0', hk_small]]
      have hinput :
          (⟨2 * k - 1, by omega⟩ : Fin N) = ⟨(2 * k - 2) + 1, by omega⟩ := by
        apply Fin.ext
        simpa using (show (((2 * k - 2) + 1 : ℕ) = 2 * k - 1) by omega).symm
      rw [hinput]
      rw [realModeToRaw_succ_even (N := N) (n := 2 * k - 2) (hm := by omega) hn_even]
      apply Fin.ext
      simpa using show (((2 * k - 2) / 2 + 1 : ℕ) = k) by omega
    · have hk_not_small : ¬ 2 * k ≤ N := hk_small
      have hk0' : k ≠ 0 := hk0
      have hn_odd : (2 * (N - k) - 1) % 2 ≠ 0 := by omega
      rw [show rawModeToReal (N := N) ⟨k, hk⟩ = ⟨2 * (N - k), by omega⟩ by
        simp [rawModeToReal, hk0', hk_not_small]]
      have hinput :
          (⟨2 * (N - k), by omega⟩ : Fin N) = ⟨(2 * (N - k) - 1) + 1, by omega⟩ := by
        apply Fin.ext
        simpa using (show (((2 * (N - k) - 1) + 1 : ℕ) = 2 * (N - k)) by omega).symm
      rw [hinput]
      rw [realModeToRaw_succ_odd (N := N) (n := 2 * (N - k) - 1) (hm := by omega) hn_odd]
      apply Fin.ext
      simpa using show ((N - ((2 * (N - k) - 1) / 2 + 1) : ℕ) = k) by omega

/-- Equivalence between real Fourier mode labels and raw torus frequencies. -/
private noncomputable def realModeRawEquiv : Fin N ≃ Fin N where
  toFun := realModeToRaw (N := N)
  invFun := rawModeToReal (N := N)
  left_inv := rawModeToReal_realModeToRaw (N := N)
  right_inv := realModeToRaw_rawModeToReal (N := N)

/-- The raw torus frequency selected by `realModeToRaw` has the same
1D lattice eigenvalue as the real Fourier mode `m`. -/
private lemma realModeToRaw_eigenvalue (a : ℝ) (m : Fin N) :
    (4 / a ^ 2) * Real.sin (Real.pi * ((realModeToRaw (N := N) m).val : ℝ) / N) ^ 2 =
      latticeEigenvalue1d N a m := by
  rcases m with ⟨_|n, hm⟩
  · simp [realModeToRaw, latticeEigenvalue1d, SmoothMap_Circle.fourierFreq]
  · set k : ℕ := n / 2 + 1
    by_cases hn_even : n % 2 = 0
    · simp [realModeToRaw, latticeEigenvalue1d, SmoothMap_Circle.fourierFreq, hn_even]
    · have hk_le : k ≤ N := by omega
      have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      have harg :
          Real.pi * (((N - k : ℕ) : ℝ)) / N = Real.pi - Real.pi * (k : ℝ) / N := by
        rw [Nat.cast_sub hk_le]
        field_simp [hN_ne]
      rw [show realModeToRaw (N := N) ⟨n + 1, hm⟩ = ⟨N - k, by omega⟩ by
        simp [realModeToRaw, k, hn_even]]
      rw [harg, Real.sin_pi_sub]
      simp [latticeEigenvalue1d, SmoothMap_Circle.fourierFreq, k]

/-- Reindex the explicit raw 1D lattice eigenvalues from raw torus
frequencies to the real Fourier ordering used by `latticeEigenvalue1d`. -/
theorem sum_rawFrequency_eq_sum_latticeEigenvalue1d
    {α : Type*} [AddCommMonoid α] (a : ℝ) (F : ℝ → α) :
    ∑ z : ZMod N, F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z : ℝ) / N) ^ 2) =
      ∑ m : Fin N, F (latticeEigenvalue1d N a m) := by
  calc
    ∑ z : ZMod N, F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z : ℝ) / N) ^ 2)
      = ∑ k : Fin N, F ((4 / a ^ 2) * Real.sin (Real.pi * (k.val : ℝ) / N) ^ 2) := by
          simpa using
            (zmod_sum_eq_fin_sum (N := N)
              (g := fun n => F ((4 / a ^ 2) * Real.sin (Real.pi * (n : ℝ) / N) ^ 2)))
    _ = ∑ m : Fin N, F (latticeEigenvalue1d N a m) := by
          symm
          refine Fintype.sum_equiv (realModeRawEquiv (N := N))
            (fun m : Fin N => F (latticeEigenvalue1d N a m))
            (fun k : Fin N =>
              F ((4 / a ^ 2) * Real.sin (Real.pi * (k.val : ℝ) / N) ^ 2)) ?_
          intro m
          symm
          exact congrArg F (realModeToRaw_eigenvalue (N := N) a m)

/-- Product version of `sum_rawFrequency_eq_sum_latticeEigenvalue1d`. -/
theorem sum_rawFrequency_pair_eq_sum_latticeEigenvalue1d_pair
    {α : Type*} [AddCommMonoid α] (a : ℝ) (F : ℝ → ℝ → α) :
    ∑ z₁ : ZMod N, ∑ z₂ : ZMod N,
      F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2)
        ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₂ : ℝ) / N) ^ 2) =
      ∑ m₁ : Fin N, ∑ m₂ : Fin N,
        F (latticeEigenvalue1d N a m₁) (latticeEigenvalue1d N a m₂) := by
  calc
    ∑ z₁ : ZMod N, ∑ z₂ : ZMod N,
        F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2)
          ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₂ : ℝ) / N) ^ 2)
      = ∑ z₁ : ZMod N, ∑ m₂ : Fin N,
          F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2)
            (latticeEigenvalue1d N a m₂) := by
              refine Finset.sum_congr rfl ?_
              intro z₁ hz₁
              simpa using
                (sum_rawFrequency_eq_sum_latticeEigenvalue1d (N := N) (a := a)
                  (F := fun t =>
                    F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2) t))
    _ = ∑ m₂ : Fin N, ∑ z₁ : ZMod N,
          F ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2)
            (latticeEigenvalue1d N a m₂) := by
              rw [Finset.sum_comm]
    _ = ∑ m₂ : Fin N, ∑ m₁ : Fin N,
          F (latticeEigenvalue1d N a m₁) (latticeEigenvalue1d N a m₂) := by
              refine Finset.sum_congr rfl ?_
              intro m₂ hm₂
              simpa using
                (sum_rawFrequency_eq_sum_latticeEigenvalue1d (N := N) (a := a)
                  (F := fun t => F t (latticeEigenvalue1d N a m₂)))
    _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
          F (latticeEigenvalue1d N a m₁) (latticeEigenvalue1d N a m₂) := by
              rw [Finset.sum_comm]

/-- Reindex lattice sites from `ZMod N` coordinates to `Fin N` coordinates. -/
private noncomputable def finLatticeSitesEquivPiFin (d : ℕ) :
    FinLatticeSites d N ≃ (Fin d → Fin N) where
  toFun x i := ⟨ZMod.val (x i), ZMod.val_lt (x i)⟩
  invFun k i := ((k i : Fin N) : ZMod N)
  left_inv x := by
    funext i
    exact ZMod.natCast_zmod_val (x i)
  right_inv k := by
    funext i
    apply Fin.ext
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt (k i).isLt]

/-- Coordinatewise version of `realModeRawEquiv`. -/
private noncomputable def realModeRawEquivFamily (d : ℕ) :
    (Fin d → Fin N) ≃ (Fin d → Fin N) where
  toFun k i := realModeToRaw (N := N) (k i)
  invFun k i := rawModeToReal (N := N) (k i)
  left_inv k := by
    funext i
    exact rawModeToReal_realModeToRaw (N := N) (k i)
  right_inv k := by
    funext i
    exact realModeToRaw_rawModeToReal (N := N) (k i)

/-- The explicit `d`-dimensional lattice eigenvalue enumeration can be
reindexed as a sum over coordinatewise 1D Fourier-mode eigenvalues. -/
theorem sum_latticeEigenvalue_eq_sum_latticeEigenvalue1d_family
    {α : Type*} [AddCommMonoid α] (d : ℕ) (a mass : ℝ) (F : ℝ → α) :
    ∑ m : Fin (Fintype.card (FinLatticeSites d N)), F (latticeEigenvalue d N a mass m) =
      ∑ k : (Fin d → Fin N),
        F ((∑ i : Fin d, latticeEigenvalue1d N a (k i)) + mass ^ 2) := by
  calc
    ∑ m : Fin (Fintype.card (FinLatticeSites d N)), F (latticeEigenvalue d N a mass m)
      = ∑ s : FinLatticeSites d N,
          F (((4 / a ^ 2) * ∑ i : Fin d,
            Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2) := by
              refine Fintype.sum_equiv (Fintype.equivFin (FinLatticeSites d N)).symm
                (fun m : Fin (Fintype.card (FinLatticeSites d N)) =>
                  F (latticeEigenvalue d N a mass m))
                (fun s : FinLatticeSites d N =>
                  F (((4 / a ^ 2) * ∑ i : Fin d,
                    Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2)) ?_
              intro m
              have hm : (m : ℕ) < N ^ d := by
                simpa using m.2
              simp [latticeEigenvalue, latticeLaplacianEigenvalue, hm]
    _ = ∑ raw : (Fin d → Fin N),
          F (((4 / a ^ 2) * ∑ i : Fin d,
            Real.sin (Real.pi * ((raw i).val : ℝ) / N) ^ 2) + mass ^ 2) := by
              refine Fintype.sum_equiv (finLatticeSitesEquivPiFin (N := N) d)
                (fun s : FinLatticeSites d N =>
                  F (((4 / a ^ 2) * ∑ i : Fin d,
                    Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2))
                (fun raw : Fin d → Fin N =>
                  F (((4 / a ^ 2) * ∑ i : Fin d,
                    Real.sin (Real.pi * ((raw i).val : ℝ) / N) ^ 2) + mass ^ 2)) ?_
              intro s
              rfl
    _ = ∑ k : (Fin d → Fin N),
          F ((∑ i : Fin d, latticeEigenvalue1d N a (k i)) + mass ^ 2) := by
              symm
              refine Fintype.sum_equiv (realModeRawEquivFamily (N := N) d)
                (fun k : Fin d → Fin N =>
                  F ((∑ i : Fin d, latticeEigenvalue1d N a (k i)) + mass ^ 2))
                (fun raw : Fin d → Fin N =>
                  F (((4 / a ^ 2) * ∑ i : Fin d,
                    Real.sin (Real.pi * ((raw i).val : ℝ) / N) ^ 2) + mass ^ 2)) ?_
              intro k
              symm
              exact congrArg F <| by
                rw [Finset.mul_sum]
                refine congrArg (fun t : ℝ => t + mass ^ 2) ?_
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact realModeToRaw_eigenvalue (N := N) a (k i)

/-- Reindex the finite 2D lattice eigenvalue enumeration into the product
ordering coming from the 1D DFT eigenvalues. -/
theorem sum_latticeEigenvalue_two_eq_sum_latticeEigenvalue1d_pair
    {α : Type*} [AddCommMonoid α] (a mass : ℝ) (F : ℝ → α) :
    ∑ m : Fin (Fintype.card (FinLatticeSites 2 N)), F (latticeEigenvalue 2 N a mass m) =
      ∑ m₁ : Fin N, ∑ m₂ : Fin N,
        F (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) := by
  let siteEquiv : FinLatticeSites 2 N ≃ ZMod N × ZMod N :=
    { toFun := fun x => (x 0, x 1)
      invFun := fun p i => Fin.cases p.1 (fun _ => p.2) i
      left_inv := by
        intro x
        ext i
        fin_cases i <;> rfl
      right_inv := by
        intro p
        rfl }
  calc
    ∑ m : Fin (Fintype.card (FinLatticeSites 2 N)), F (latticeEigenvalue 2 N a mass m)
      = ∑ s : FinLatticeSites 2 N,
          F (((4 / a ^ 2) * ∑ i : Fin 2,
            Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2) := by
              refine Fintype.sum_equiv (Fintype.equivFin (FinLatticeSites 2 N)).symm
                (fun m : Fin (Fintype.card (FinLatticeSites 2 N)) =>
                  F (latticeEigenvalue 2 N a mass m))
                (fun s : FinLatticeSites 2 N =>
                  F (((4 / a ^ 2) * ∑ i : Fin 2,
                    Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2)) ?_
              intro m
              have hm' : (m : ℕ) < N ^ 2 := by
                simpa using m.2
              simp [latticeEigenvalue, latticeLaplacianEigenvalue, hm']
    _ = ∑ p : ZMod N × ZMod N,
          F (((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val p.1 : ℝ) / N) ^ 2) +
            ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val p.2 : ℝ) / N) ^ 2) + mass ^ 2) := by
              refine Fintype.sum_equiv siteEquiv
                (fun s : FinLatticeSites 2 N =>
                  F (((4 / a ^ 2) * ∑ i : Fin 2,
                    Real.sin (Real.pi * (ZMod.val (s i) : ℝ) / N) ^ 2) + mass ^ 2))
                (fun p : ZMod N × ZMod N =>
                  F (((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val p.1 : ℝ) / N) ^ 2) +
                    ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val p.2 : ℝ) / N) ^ 2) +
                    mass ^ 2)) ?_
              intro s
              simp [siteEquiv]
              congr 1
              ring
    _ = ∑ z₁ : ZMod N, ∑ z₂ : ZMod N,
          F (((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₁ : ℝ) / N) ^ 2) +
            ((4 / a ^ 2) * Real.sin (Real.pi * (ZMod.val z₂ : ℝ) / N) ^ 2) + mass ^ 2) := by
              rw [Fintype.sum_prod_type]
    _ = ∑ m₁ : Fin N, ∑ m₂ : Fin N,
          F (latticeEigenvalue1d N a m₁ + latticeEigenvalue1d N a m₂ + mass ^ 2) := by
              exact sum_rawFrequency_pair_eq_sum_latticeEigenvalue1d_pair (N := N) (a := a)
                (F := fun x y => F (x + y + mass ^ 2))

end GaussianField
