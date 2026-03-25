/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Periodization: Schwartz → Smooth Circle

Defines the periodization map `𝓢(ℝ) →L[ℝ] C∞(S¹_L)` that wraps a
Schwartz function onto a circle of period L by summing translates:

  `(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

## Main definitions

- `periodizeCLM L` — the continuous linear periodization map

## Mathematical background

For `h ∈ 𝓢(ℝ)`, the rapid decay `|h^(n)(t)| ≤ C_{N,n} (1+|t|)^{-N}`
guarantees that the sum `Σ_k h^(n)(t + kL)` converges absolutely and
uniformly on `[0, L]` for any `n` and any `N > 1`. This gives:

1. **Smoothness**: derivatives commute with the sum
2. **Periodicity**: `Σ_k h(t+L+kL) = Σ_k h(t+kL)` by reindexing
3. **Continuity**: Schwartz seminorms control circle Sobolev seminorms

## References

- Stein-Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Ch. VII
- Grafakos, *Classical Fourier Analysis*, §3.1.2
-/

import SmoothCircle.Nuclear
import SchwartzNuclear.HermiteNuclear
import Torus.Symmetry
import Cylinder.Symmetry

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Periodization: raw function and basic properties -/

/-- The periodization function: `(periodizeFun L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`. -/
def periodizeFun (h : SchwartzMap ℝ ℝ) (t : ℝ) : ℝ := ∑' (k : ℤ), h (t + k * L)

/-- The sum `Σ_k h(t + kL)` converges absolutely for each `t` when `h` is Schwartz.

**Proof**: By `SchwartzMap.norm_pow_mul_le_seminorm` with `k = 2`:
`‖x‖² · ‖h(x)‖ ≤ (seminorm ℝ 2 0) h`, so `‖h(x)‖ ≤ S/‖x‖²` for `‖x‖ > 0`.
Split ℤ into positive and negative halves. For `n ≥ ⌈2|t|/L⌉ + 1`,
`‖t + nL‖ ≥ nL/2`, giving `‖h(t + nL)‖ ≤ 4S/(nL)²`. The bounding series
`Σ_n 4S/(nL)² = (4S/L²) Σ 1/n²` converges by `Real.summable_one_div_nat_pow`.

Reference: Grafakos, *Classical Fourier Analysis*, Proposition 3.1.15. -/
theorem periodize_summable (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    Summable (fun k : ℤ => h (t + k * L)) := by
  rw [summable_int_iff_summable_nat_and_neg]
  set S := (SchwartzMap.seminorm ℝ 2 0) h
  have hL_pos := hL.out
  have norm_bound : ∀ x : ℝ, ‖x‖ ^ 2 * ‖h x‖ ≤ S :=
    fun x => SchwartzMap.norm_pow_mul_le_seminorm ℝ h 2 x
  -- If d ≤ ‖x‖ and d > 0, then ‖h x‖ ≤ S / d²
  have bound_from_lower (x d : ℝ) (hd : 0 < d) (hxd : d ≤ ‖x‖) :
      ‖h x‖ ≤ S / d ^ 2 := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < d ^ 2)]
    have : d ^ 2 ≤ ‖x‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x‖ - d), sq_nonneg ‖x‖, sq_nonneg d]
    calc ‖h x‖ * d ^ 2 ≤ ‖h x‖ * ‖x‖ ^ 2 := by nlinarith [norm_nonneg (h x)]
      _ = ‖x‖ ^ 2 * ‖h x‖ := by ring
      _ ≤ S := norm_bound x
  -- Threshold: for n ≥ N, nL ≥ 2|t|, so |t ± nL| ≥ nL/2
  set N := ⌈2 * |t| / L⌉₊ + 1
  have hN_bound : ∀ n : ℕ, N ≤ n → 2 * |t| ≤ ↑n * L := by
    intro n hn
    have hn_cast : (⌈2 * |t| / L⌉₊ : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    calc 2 * |t| = (2 * |t| / L) * L := by field_simp
      _ ≤ ↑⌈2 * |t| / L⌉₊ * L := by nlinarith [Nat.le_ceil (2 * |t| / L)]
      _ ≤ ↑n * L := by nlinarith
  constructor
  · -- Positive half: Summable (fun n : ℕ => h (t + ↑n * L))
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n => (4 * S / L ^ 2) * (1 / (n : ℝ) ^ 2))
      (((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left _) ?_
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have := hN_bound n hn
    calc ‖h (t + ↑n * L)‖
        ≤ S / (↑n * L / 2) ^ 2 := by
          apply bound_from_lower
          · positivity
          · rw [Real.norm_eq_abs, abs_of_nonneg (by nlinarith [neg_abs_le t])]
            nlinarith [neg_abs_le t]
      _ = 4 * S / L ^ 2 * (1 / ↑n ^ 2) := by ring
  · -- Negative half: Summable (fun n : ℕ => h (t + (-↑n) * L))
    suffices Summable (fun n : ℕ => h (t - ↑n * L)) by
      convert this using 1; ext n; congr 1; push_cast; ring
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n => (4 * S / L ^ 2) * (1 / (n : ℝ) ^ 2))
      (((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left _) ?_
    rw [Filter.eventually_atTop]
    refine ⟨N, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have := hN_bound n hn
    calc ‖h (t - ↑n * L)‖
        ≤ S / (↑n * L / 2) ^ 2 := by
          apply bound_from_lower
          · positivity
          · rw [Real.norm_eq_abs, abs_of_nonpos (by nlinarith [le_abs_self t])]
            nlinarith [le_abs_self t]
      _ = 4 * S / L ^ 2 * (1 / ↑n ^ 2) := by ring

/-- The periodized function is periodic with period `L`.

**Proof**: Reindex the sum using `k ↦ k + 1`:
`Σ_k h(t + L + kL) = Σ_k h(t + (k+1)L) = Σ_j h(t + jL)`.
Uses `Equiv.tsum_eq` with the equivalence `k ↦ k + 1` on `ℤ`.

Note: `hL` is not needed; periodicity is purely algebraic (reindexing). -/
theorem periodizeFun_periodic (h : SchwartzMap ℝ ℝ) :
    Function.Periodic (periodizeFun L h) L := by
  intro t
  simp only [periodizeFun]
  -- Rewrite each term: h(t + L + kL) = h(t + (k+1)L)
  have h_rw : (fun k : ℤ => h (t + L + ↑k * L)) =
      (fun k : ℤ => h (t + (↑k + 1) * L)) :=
    funext fun k => by ring_nf
  rw [h_rw]
  -- Reindex with j = k + 1 using Equiv.tsum_eq
  rw [show (fun k : ℤ => h (t + (↑k + 1) * L)) =
    (fun k : ℤ => (fun j : ℤ => h (t + ↑j * L)) ((Equiv.addRight (1 : ℤ)) k)) from by
    ext k; simp [Equiv.addRight]]
  exact Equiv.tsum_eq (Equiv.addRight (1 : ℤ)) (fun j : ℤ => h (t + ↑j * L))

/-- `iteratedFDeriv` of a function that's locally zero vanishes. -/
private lemma iteratedFDeriv_eq_zero_of_eventuallyEq_zero
    (f : ℝ → ℝ) (x : ℝ) (m : ℕ) (hf : f =ᶠ[nhds x] 0) :
    iteratedFDeriv ℝ m f x = 0 := by
  rw [(hf.iteratedFDeriv ℝ m).eq_of_nhds]; exact congr_fun iteratedFDeriv_zero_fun x

/-- `φ · g` vanishes near `x` when `x ∉ tsupport φ` (since `φ = 0` on the open complement). -/
private lemma mul_eventuallyEq_zero_outside_tsupport
    (φ g : ℝ → ℝ) (x : ℝ) (hx : x ∉ tsupport φ) :
    (fun t => φ t * g t) =ᶠ[nhds x] 0 := by
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨(tsupport φ)ᶜ, (isClosed_tsupport φ).isOpen_compl.mem_nhds hx, fun y hy => by
      simp [Function.notMem_support.mp (fun h => hy (subset_tsupport φ h))]⟩

/-- Leibniz + Schwartz decay bound on the support of `φ`.

For `x ∈ tsupport φ` and `|x + kL| ≥ 1`, the Leibniz rule gives:
  `‖D^m(φ · h(·+kL))(x)‖ ≤ Σ_{j≤m} C(m,j) · ‖D^j φ(x)‖ · ‖D^{m-j} h(x+kL)‖`
Each `‖D^j φ(x)‖` is bounded (continuous on compact `tsupport φ`).
Each `‖D^{m-j} h(x+kL)‖ ≤ S_{2,m-j} / |x+kL|²` by `SchwartzMap.le_seminorm'`.

Remaining formalization: `iteratedDeriv_fun_mul` + `norm_sum_le` for the Leibniz norm
bound, `IsCompact.exists_isMaxOn` for `‖D^j φ‖` on compact support,
`SchwartzMap.le_seminorm'` with `k = 2` for each Schwartz derivative factor. -/
private theorem iteratedFDeriv_product_bound_on_support
    (h : SchwartzMap ℝ ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcomp : HasCompactSupport φ) (m : ℕ) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (k : ℤ) (x : ℝ), x ∈ tsupport φ → |x + ↑k * L| ≥ 1 →
      ‖iteratedFDeriv ℝ m (fun t => φ t * h (t + ↑k * L)) x‖ ≤
        C / |x + ↑k * L| ^ 2 := by
  -- Bounds on φ derivatives (compact support + continuity)
  have hφ_bound : ∀ j : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, ‖iteratedDeriv j φ x‖ ≤ B := by
    intro j
    obtain ⟨B, hB⟩ := (hcomp.iteratedFDeriv j).exists_bound_of_continuous
      (hφ.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top))
    exact ⟨B, le_trans (norm_nonneg _) (hB 0), fun x => by
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]; exact hB x⟩
  choose B hB_nn hB using hφ_bound
  -- Schwartz seminorms: ‖y‖^2 * ‖D^n h y‖ ≤ S n
  set S := fun n => (SchwartzMap.seminorm ℝ 2 n) h
  have hS_nn : ∀ n, 0 ≤ S n := fun n => apply_nonneg _ _
  have hSchwartz : ∀ n y, ‖y‖ ^ 2 * ‖iteratedDeriv n (⇑h) y‖ ≤ S n := by
    intro n y; have := SchwartzMap.le_seminorm ℝ 2 n h y
    rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at this
  -- The constant: Σ C(m,i) * B_i * S_{m-i}
  set C₀ := ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * B i * S (m - i)
  have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB_nn i)) (hS_nn _)
  refine ⟨C₀, hC₀_nn, ?_⟩
  intro k x _ hxkL
  have hxkL_pos : 0 < |x + ↑k * L| := lt_of_lt_of_le one_pos hxkL
  -- ContDiffAt hypotheses for Leibniz rule
  have hφ_cda : ContDiffAt ℝ m φ x :=
    hφ.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg_cda : ContDiffAt ℝ m (fun t => h (t + ↑k * L)) x :=
    ((h.smooth ⊤).comp (contDiff_id.add contDiff_const)).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  -- Convert to iteratedDeriv and apply Leibniz rule
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_fun_mul hφ_cda hg_cda]
  -- Bound each Leibniz term
  have h_term : ∀ i ∈ Finset.range (m + 1),
      ‖(m.choose i : ℝ) * iteratedDeriv i φ x *
        iteratedDeriv (m - i) (fun t => h (t + ↑k * L)) x‖ ≤
      (m.choose i : ℝ) * B i * S (m - i) / |x + ↑k * L| ^ 2 := by
    intro i _
    rw [norm_mul, norm_mul, Real.norm_natCast]
    -- D^{m-i}(h(· + kL))(x) = D^{m-i} h (x + kL) by translation invariance
    rw [show iteratedDeriv (m - i) (fun t => h (t + ↑k * L)) x =
        iteratedDeriv (m - i) (⇑h) (x + ↑k * L) from
        congrFun (iteratedDeriv_comp_add_const _ _ _) _]
    -- Schwartz bound: ‖D^{m-i} h y‖ ≤ S(m-i) / |y|^2
    have h_schwartz_bound : ‖iteratedDeriv (m - i) (⇑h) (x + ↑k * L)‖ ≤
        S (m - i) / |x + ↑k * L| ^ 2 := by
      have hle := hSchwartz (m - i) (x + ↑k * L)
      rw [Real.norm_eq_abs] at hle
      rwa [le_div_iff₀ (by positivity : (0:ℝ) < |x + ↑k * L| ^ 2), mul_comm]
    calc (m.choose i : ℝ) * ‖iteratedDeriv i φ x‖ *
            ‖iteratedDeriv (m - i) (⇑h) (x + ↑k * L)‖
        ≤ (m.choose i : ℝ) * B i * (S (m - i) / |x + ↑k * L| ^ 2) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hB i x) (Nat.cast_nonneg _))
            h_schwartz_bound (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB_nn i))
      _ = (m.choose i : ℝ) * B i * S (m - i) / |x + ↑k * L| ^ 2 := by ring
  calc ‖∑ i ∈ Finset.range (m + 1), _‖
      ≤ ∑ i ∈ Finset.range (m + 1), ‖_‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * B i * S (m - i) / |x + ↑k * L| ^ 2 :=
        Finset.sum_le_sum h_term
    _ = C₀ / |x + ↑k * L| ^ 2 := by rw [← Finset.sum_div]

/-- For a compactly supported C^∞ bump function `φ` and a Schwartz function `h`,
the iterated Fréchet derivatives of the product `φ · h(· + kL)` decay like `O(1/k²)`
for large `|k|`.

The proof case-splits on `x ∈ tsupport φ`:
- **Outside support**: `φ · h(· + kL)` vanishes on a neighborhood of `x`
  (via `mul_eventuallyEq_zero_outside_tsupport`), so `iteratedFDeriv = 0`
  (via `iteratedFDeriv_eq_zero_of_eventuallyEq_zero`).
- **On support**: `iteratedFDeriv_product_bound_on_support` gives
  `‖D^m(φ · h(·+kL))(x)‖ ≤ C₀ / |x+kL|²`. Since `|x| ≤ R` and `|kL| > 2R`,
  `|x+kL| ≥ |kL|/2`, giving `C₀/|x+kL|² ≤ 4C₀/(|k|L)²`. -/
private theorem iteratedFDeriv_mul_schwartz_decay
    (h : SchwartzMap ℝ ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcomp : HasCompactSupport φ) (m : ℕ) :
    ∃ (C : ℝ) (K : ℕ), 0 ≤ C ∧ ∀ (k : ℤ), (K : ℤ) < |k| →
      ∀ x : ℝ, ‖iteratedFDeriv ℝ m (fun t => φ t * h (t + ↑k * L)) x‖ ≤
        C / (↑|k| * L) ^ 2 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hcomp.isBounded
  obtain ⟨C₀, hC₀, hbound_supp⟩ :=
    iteratedFDeriv_product_bound_on_support L h φ hφ hcomp m
  have hL_pos := hL.out
  refine ⟨4 * C₀, ⌈(2 * max R 1) / L⌉₊ + 1, by linarith, ?_⟩
  intro k hkK x
  by_cases hx : x ∈ tsupport φ
  · -- On support: use hbound_supp + |x+kL| ≥ |kL|/2
    have hxR : |x| ≤ R := by
      have := hR hx; simp [Metric.mem_closedBall, dist_zero_right] at this; exact this
    -- Step 1: 2 * max R 1 ≤ |k|L (from hkK)
    have h2M : 2 * max R 1 ≤ (↑|k| : ℝ) * L := by
      have h1 : (2 * max R 1 / L : ℝ) ≤ ↑(⌈2 * max R 1 / L⌉₊ + 1 : ℕ) := by
        push_cast; linarith [Nat.le_ceil (2 * max R 1 / L)]
      have h2 : (↑(⌈2 * max R 1 / L⌉₊ + 1 : ℕ) : ℝ) < (↑|k| : ℝ) := by exact_mod_cast hkK
      nlinarith [div_mul_cancel₀ (2 * max R 1) (ne_of_gt hL_pos)]
    -- Step 2: |x + kL| ≥ |k|L/2 (reverse triangle + |x| ≤ R ≤ |k|L/2)
    have h_abs_kL : |↑k * L| = (↑|k| : ℝ) * L := by
      rw [abs_mul, abs_of_pos hL_pos]; push_cast; rfl
    have h_lower : (↑|k| : ℝ) * L / 2 ≤ |x + ↑k * L| := by
      have h1 : (↑|k| : ℝ) * L ≤ |x + ↑k * L| + |x| := by
        calc (↑|k| : ℝ) * L = |↑k * L| := h_abs_kL.symm
          _ = |(x + ↑k * L) + (-x)| := by ring_nf
          _ ≤ |x + ↑k * L| + |-x| := abs_add_le _ _
          _ = |x + ↑k * L| + |x| := by rw [abs_neg]
      linarith [le_max_left R 1]
    -- Step 3: |x + kL| ≥ 1
    have h_ge_1 : 1 ≤ |x + ↑k * L| := by linarith [le_max_right R 1]
    -- Step 4: apply hbound_supp, then bound C₀/|x+kL|² ≤ 4C₀/(|k|L)²
    calc ‖iteratedFDeriv ℝ m (fun t => φ t * h (t + ↑k * L)) x‖
        ≤ C₀ / |x + ↑k * L| ^ 2 := hbound_supp k x hx (by linarith)
      _ ≤ C₀ / ((↑|k| : ℝ) * L / 2) ^ 2 := by
          have hkL_pos : 0 < (↑|k| : ℝ) * L / 2 := by
            have : 0 < (↑|k| : ℝ) * L := by linarith [le_max_right R 1]
            linarith
          apply div_le_div_of_nonneg_left hC₀ (sq_pos_of_pos hkL_pos)
            (pow_le_pow_left₀ hkL_pos.le h_lower 2)
      _ = 4 * C₀ / ((↑|k| : ℝ) * L) ^ 2 := by ring
  · -- Outside support: product vanishes locally
    have h0 := iteratedFDeriv_eq_zero_of_eventuallyEq_zero
      (fun t => φ t * h (t + ↑k * L)) x m
      (mul_eventuallyEq_zero_outside_tsupport φ (fun t => h (t + ↑k * L)) x hx)
    simp [h0]; exact div_nonneg (by linarith) (sq_nonneg _)

/-- `C / (|k| * L)²` is summable over `ℤ` (follows from `Σ 1/k²` converging). -/
private lemma summable_inv_int_sq_mul (C L : ℝ) :
    Summable (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) := by
  have heq : (fun k : ℤ => C / ((↑|k| : ℝ) * L) ^ 2) =
      (fun k : ℤ => (C / L ^ 2) * (1 / (↑|k| : ℝ) ^ 2)) := by ext k; ring
  rw [heq]; apply Summable.mul_left
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩ <;> {
    exact ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).congr
      fun n => by simp [abs_of_nonneg (Int.natCast_nonneg n), abs_neg]
  }

/-- The product `φ · h(· + kL)` has `iteratedFDeriv` bounded by a summable function of `k`,
for cofinitely many `k`. Combines `iteratedFDeriv_mul_schwartz_decay` (the `O(1/k²)` bound)
with `summable_inv_int_sq_mul` (summability of `1/k²` over `ℤ`). -/
private theorem bump_periodize_iteratedFDeriv_bound
    (h : SchwartzMap ℝ ℝ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hcomp : HasCompactSupport φ) :
    ∃ (v : ℕ → ℤ → ℝ), (∀ m, Summable (v m)) ∧
    ∀ m : ℕ, ∀ᶠ (k : ℤ) in Filter.cofinite,
      ∀ x : ℝ, ‖iteratedFDeriv ℝ m (fun t => φ t * h (t + ↑k * L)) x‖ ≤ v m k := by
  choose C K hC hbound using
    fun m => iteratedFDeriv_mul_schwartz_decay L h φ hφ hcomp m
  -- v m k = C m / (|k| * L)²
  set v : ℕ → ℤ → ℝ := fun m k => C m / (↑|k| * L) ^ 2
  have hv_sum : ∀ m, Summable (v m) := fun m => summable_inv_int_sq_mul (C m) L
  have hv_cof : ∀ m : ℕ, ∀ᶠ (k : ℤ) in Filter.cofinite,
      ∀ x : ℝ, ‖iteratedFDeriv ℝ m (fun t => φ t * h (t + ↑k * L)) x‖ ≤ v m k := by
    intro m; rw [Filter.eventually_cofinite]
    refine (Set.finite_Icc (-(K m : ℤ)) (K m : ℤ)).subset ?_
    intro k hk
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hk
    obtain ⟨x, hx⟩ := hk
    rw [Set.mem_Icc]; by_contra habs
    simp only [not_and_or, not_le] at habs
    have hkK : (K m : ℤ) < |k| := by
      rcases habs with h | h
      · rw [abs_of_neg (by omega : k < 0)]; omega
      · rw [abs_of_pos (by omega : 0 < k)]; omega
    exact absurd (hbound m k hkK x) (not_le.mpr hx)
  exact ⟨v, hv_sum, hv_cof⟩

/-- The periodized sum is smooth (`C∞`).

**Proof**: We reduce to `ContDiffAt` at each point using `contDiff_iff_contDiffAt`.
At each `t₀`, we use a smooth bump function `φ` with `φ(t₀) = 1` and compact support
(from `exists_contDiff_tsupport_subset`). The key observation is:

  `φ(t) · periodizeFun L h (t) = Σ_k φ(t) · h(t + kL)`

The right side is `ContDiff ℝ ⊤` by `contDiff_tsum_of_eventually`, using the bound from
`bump_periodize_iteratedFDeriv_bound`: each product `φ · h(· + kL)` is compactly supported,
so the iterated derivatives have globally summable bounds (via Schwartz decay of `h`).

Since `φ(t₀) = 1 ≠ 0`, we recover `periodizeFun L h = (φ · periodizeFun) · φ⁻¹` near `t₀`,
which is `ContDiffAt` as a product of smooth functions (`ContDiffAt.mul`, `ContDiffAt.inv`).

Reference: Grafakos, *Classical Fourier Analysis*, §3.1.2. -/
theorem periodize_smooth (h : SchwartzMap ℝ ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (periodizeFun L h) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  -- Get a bump function φ with φ(t₀) = 1 and compact support near t₀
  obtain ⟨φ, _, hcomp, hsmooth, _, hone⟩ :=
    exists_contDiff_tsupport_subset
      (s := Set.Ioo (t₀ - 1) (t₀ + 1)) (n := ⊤) (x := t₀)
      (Ioo_mem_nhds (by linarith) (by linarith))
  -- Each term φ(·) * h(· + kL) is C^∞
  have hterm : ∀ k : ℤ, ContDiff ℝ (⊤ : ℕ∞) (fun t => φ t * h (t + ↑k * L)) := fun k =>
    ContDiff.mul hsmooth ((h.smooth ⊤).comp (contDiff_id.add contDiff_const))
  -- Get summable bounds on iterated derivatives
  obtain ⟨v, hv_sum, hv_bound⟩ := bump_periodize_iteratedFDeriv_bound L h φ hsmooth hcomp
  -- G(t) = Σ_k φ(t) * h(t + kL) is ContDiff ℝ ⊤
  have hG_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun t => ∑' (k : ℤ), φ t * h (t + ↑k * L)) :=
    contDiff_tsum_of_eventually hterm (fun m _ => hv_sum m) (fun m _ => hv_bound m)
  -- G(t) = φ(t) * periodizeFun L h t
  have hG_eq : ∀ t, ∑' (k : ℤ), φ t * h (t + ↑k * L) = φ t * periodizeFun L h t := by
    intro t; simp only [periodizeFun]; rw [tsum_mul_left]
  -- φ(t₀) ≠ 0
  have hφ_ne : φ t₀ ≠ 0 := by rw [hone]; exact one_ne_zero
  -- On a neighborhood of t₀, φ ≠ 0
  have hφ_ev : ∀ᶠ t in nhds t₀, φ t ≠ 0 :=
    hsmooth.continuous.continuousAt.eventually_ne hφ_ne
  -- periodizeFun = G * φ⁻¹ near t₀
  have heq : periodizeFun L h =ᶠ[nhds t₀]
      fun t => (∑' (k : ℤ), φ t * h (t + ↑k * L)) * (φ t)⁻¹ := by
    filter_upwards [hφ_ev] with t ht
    rw [hG_eq, mul_comm (φ t) _, mul_assoc, mul_inv_cancel₀ ht, mul_one]
  -- ContDiffAt of (G * φ⁻¹) at t₀, then transfer to periodizeFun
  exact (ContDiffAt.mul hG_contDiff.contDiffAt
    (ContDiffAt.inv hsmooth.contDiffAt hφ_ne)).congr_of_eventuallyEq heq

/-- The periodized function as an element of `SmoothMap_Circle L ℝ`. -/
def periodizeSmoothCircle (h : SchwartzMap ℝ ℝ) : SmoothMap_Circle L ℝ :=
  ⟨periodizeFun L h, periodizeFun_periodic L h, periodize_smooth L h⟩

@[simp] theorem periodizeSmoothCircle_toFun (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    (periodizeSmoothCircle L h).toFun t = ∑' (k : ℤ), h (t + k * L) := rfl

/-! ## Linearity of periodization -/

theorem periodizeSmoothCircle_add (f g : SchwartzMap ℝ ℝ) :
    periodizeSmoothCircle L (f + g) =
    periodizeSmoothCircle L f + periodizeSmoothCircle L g := by
  apply SmoothMap_Circle.ext; intro t
  unfold periodizeSmoothCircle
  simp only [SmoothMap_Circle.add_apply, SmoothMap_Circle.coe_mk, periodizeFun]
  simp only [SchwartzMap.add_apply]
  exact (periodize_summable L f t).tsum_add (periodize_summable L g t)

theorem periodizeSmoothCircle_smul (r : ℝ) (h : SchwartzMap ℝ ℝ) :
    periodizeSmoothCircle L (r • h) = r • periodizeSmoothCircle L h := by
  apply SmoothMap_Circle.ext; intro t
  unfold periodizeSmoothCircle
  simp only [SmoothMap_Circle.smul_apply, SmoothMap_Circle.coe_mk, periodizeFun]
  rw [show (fun k : ℤ => (r • h) (t + ↑k * L)) =
    (fun k : ℤ => r • h (t + ↑k * L)) from by ext k; rfl]
  rw [tsum_const_smul'' r, smul_eq_mul]

/-- The periodization linear map (without continuity). -/
def periodizeLM : SchwartzMap ℝ ℝ →ₗ[ℝ] SmoothMap_Circle L ℝ where
  toFun := periodizeSmoothCircle L
  map_add' := periodizeSmoothCircle_add L
  map_smul' r h := by simp [periodizeSmoothCircle_smul]

/-! ## CLM continuity -/

/-- The Sobolev seminorm of the periodized function is bounded by Schwartz seminorms.

For each Sobolev order `k`, we have:
`sobolevSeminorm k (periodize h) ≤ C_{k,L} · (seminorm ℝ (k+2) k) h`

**Proof sketch**: The k-th derivative of the periodized function satisfies
`|D^k (periodize h)(t)| = |Σ_j D^k h(t + jL)| ≤ Σ_j |h^(k)(t + jL)|`.
By `SchwartzMap.le_seminorm'`, `|x|^(k+2) · |h^(k)(x)| ≤ (seminorm ℝ (k+2) k) h`,
so `|h^(k)(t + jL)| ≤ (seminorm ℝ (k+2) k) h / |t + jL|^(k+2)`.
The sum `Σ_j 1/|t + jL|^(k+2)` converges (uniformly in `t ∈ [0,L]`) since `k+2 ≥ 2 > 1`.

Reference: Stein-Weiss, Ch. VII, §2. -/
axiom periodize_sobolevSeminorm_le (k : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
      ∀ (h : SchwartzMap ℝ ℝ),
        SmoothMap_Circle.sobolevSeminorm k (periodizeSmoothCircle L h) ≤
        C * (s.sup (schwartzSeminormFamily ℝ ℝ ℝ)) h

/-! ## Periodization CLM -/

/-- The periodization map from Schwartz space to smooth periodic functions.

`(periodize L h)(t) = Σ_{k ∈ ℤ} h(t + kL)`

Constructed as a continuous linear map using:
- `periodizeSmoothCircle` for the underlying function
- `periodize_summable` for convergence of the sum
- `periodize_smooth` for smoothness of the sum
- `periodize_sobolevSeminorm_le` for continuity (Sobolev-Schwartz bound)

The sum converges absolutely in all Sobolev norms by rapid decay of `h`. -/
def periodizeCLM : SchwartzMap ℝ ℝ →L[ℝ] SmoothMap_Circle L ℝ where
  toLinearMap := periodizeLM L
  cont := by
    apply WithSeminorms.continuous_of_isBounded
      (schwartz_withSeminorms ℝ ℝ ℝ)
      SmoothMap_Circle.smoothCircle_withSeminorms
    intro i
    obtain ⟨s, C, hC, hbound⟩ := periodize_sobolevSeminorm_le L i
    refine ⟨s, ⟨C, hC⟩, fun h => ?_⟩
    simp only [Seminorm.comp_apply, NNReal.smul_def, Seminorm.smul_apply, NNReal.coe_mk]
    exact hbound h

/-- Pointwise formula for periodization. -/
theorem periodizeCLM_apply (h : SchwartzMap ℝ ℝ) (t : ℝ) :
    (periodizeCLM L h).toFun t = ∑' (k : ℤ), h (t + k * L) := rfl

/-- For compactly supported Schwartz functions with support in `[-T, T]`
and `L > 2T`, the periodization agrees with `h` on `[0, L/2]`.

This is because only the `k = 0` term is nonzero on `[0, L/2]`:
for `t ∈ [0, L/2]` and `k ≠ 0`, `|t + kL| ≥ L/2 > T`, so `h(t + kL) = 0`. -/
theorem periodizeCLM_eq_on_large_period (h : SchwartzMap ℝ ℝ) (T : ℝ) (hT : 0 < T)
    (hsupp : ∀ t, T < |t| → h t = 0)
    (hL_large : L > 2 * T) :
    ∀ t ∈ Set.Icc 0 (L / 2), (periodizeCLM L h).toFun t = h t := by
  intro t ht
  rw [periodizeCLM_apply]
  have hL_pos := hL.out
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    apply hsupp
    -- Show T < |t + k * L| for k ≠ 0
    rcases Int.lt_or_lt_of_ne hk with hk_neg | hk_pos
    · -- k ≤ -1: t + kL ≤ L/2 + (-1)·L = -L/2 < -T
      have : k ≤ (-1 : ℤ) := Int.le_sub_one_of_lt hk_neg
      have hkL : ↑k * L ≤ -L := by
        have : (k : ℝ) ≤ (-1 : ℝ) := by exact_mod_cast this
        nlinarith
      have : t + ↑k * L < -T := by nlinarith [ht.2]
      rw [abs_of_neg (by linarith)]
      linarith
    · -- k ≥ 1: t + kL ≥ 0 + 1·L = L > 2T > T
      have : (1 : ℤ) ≤ k := hk_pos
      have hkL : L ≤ ↑k * L := by
        have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast this
        nlinarith
      have htk : T < t + ↑k * L := by nlinarith [ht.1]
      rw [abs_of_pos (by linarith)]
      exact htk

/-! ## Intertwining with symmetries -/

/-- Periodization commutes with time translation:
`periodize L (shift_τ h) = circleTranslation L τ (periodize L h)`.

Proof: `Σ_k h(t - τ + kL) = Σ_k h((t - τ) + kL) = (periodize L h)(t - τ)`. -/
theorem periodizeCLM_comp_schwartzTranslation (τ : ℝ) (h : SchwartzMap ℝ ℝ) :
    periodizeCLM L (schwartzTranslation τ h) =
    circleTranslation L τ (periodizeCLM L h) := by
  apply SmoothMap_Circle.ext; intro t
  simp only [circleTranslation]
  show (periodizeCLM L (schwartzTranslation τ h)).toFun t =
    (periodizeCLM L h).toFun (t - τ)
  rw [periodizeCLM_apply, periodizeCLM_apply]
  congr 1; ext k
  simp [schwartzTranslation_apply]
  ring

/-- Periodization commutes with time reflection:
`periodize L (reflect h) = circleReflection L (periodize L h)`
where `reflect h(t) = h(-t)` and `circleReflection L g(t) = g(-t)`.

Proof: `Σ_k h(-t + kL) = Σ_k h(-(t - kL)) = Σ_k h(-(t + (-k)L))
= Σ_j h(-(t + jL)) = (reflect ∘ periodize L)(h)(t)`.
(Reindex `j = -k`.) -/
theorem periodizeCLM_comp_schwartzReflection (h : SchwartzMap ℝ ℝ) :
    periodizeCLM L (schwartzReflection h) =
    circleReflection L (periodizeCLM L h) := by
  apply SmoothMap_Circle.ext; intro t
  simp only [circleReflection]
  show (periodizeCLM L (schwartzReflection h)).toFun t =
    (periodizeCLM L h).toFun (-t)
  rw [periodizeCLM_apply, periodizeCLM_apply]
  -- LHS: Σ_k h(-(t + kL)), RHS: Σ_k h(-t + kL)
  -- Reindex: substitute j = -k in LHS
  rw [show (fun k : ℤ => (schwartzReflection h) (t + ↑k * L)) =
    (fun k : ℤ => h (-(t + ↑k * L))) from by ext k; simp [schwartzReflection]]
  conv_rhs => rw [← Equiv.tsum_eq (Equiv.neg ℤ)]
  congr 1; ext k; simp; ring

end GaussianField
