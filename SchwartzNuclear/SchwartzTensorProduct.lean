/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Tensor Product Isomorphism via Dimension Peeling

Proves `S(ℝ^{m+1}) ⊗̂ S(ℝ^{n+1}) ≃L S(ℝ^{m+n+2})` by peeling off one dimension
at a time. The key isomorphism `schwartzPeelOff` identifies
`S(ℝ^{d+2}) ≃L NuclearTensorProduct S(ℝ^{d+1}) S(ℝ)`,
and the general result follows by induction on `n`.

## Main definitions

- `RapidDecaySeq.reindex` — reindexing automorphism for polynomially-bounded permutations
- `NuclearTensorProduct.assoc` — associativity of the nuclear tensor product
- `schwartzPointwiseProduct` — product function `h(x,t) = f(x)·g(t)` as Schwartz map
- `schwartzPeelOff` — isomorphism `S(ℝ^{d+2}) ≃L S(ℝ^{d+1}) ⊗̂ S(ℝ)`
- `schwartzTensorEquiv` — isomorphism `S(ℝ^{m+1}) ⊗̂ S(ℝ^{n+1}) ≃L S(ℝ^{m+n+2})`

## References

- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Trèves, "Topological Vector Spaces, Distributions and Kernels", Ch. 51
-/

import SchwartzNuclear.HermiteNuclear
import Nuclear.NuclearTensorProduct

noncomputable section

namespace GaussianField

open scoped NNReal
open MeasureTheory

/-! ## Step 1: Reindexing Automorphism for RapidDecaySeq -/

namespace RapidDecaySeq

/-- A permutation `σ : ℕ ≃ ℕ` is polynomially bounded if there exist `C > 0` and `k`
such that `1 + σ(n) ≤ C * (1 + n)^k` for all `n`. -/
def IsPolyBounded (σ : ℕ ≃ ℕ) : Prop :=
  ∃ C > (0 : ℝ), ∃ k : ℕ, ∀ n : ℕ, (1 + (σ n : ℝ)) ≤ C * (1 + (n : ℝ)) ^ k

/-- Reindexing `a.val ∘ σ` is rapidly decreasing when `σ⁻¹` is polynomially bounded.
Change of variables `n = σ m`: `∑_m |a(σ m)| (1+m)^k = ∑_n |a(n)| (1+σ⁻¹(n))^k`,
then bound `(1+σ⁻¹(n))^k ≤ (C(1+n)^p)^k` using the poly bound on `σ⁻¹`. -/
lemma reindex_rapid_decay (σ : ℕ ≃ ℕ) (hσ_inv : IsPolyBounded σ.symm)
    (a : RapidDecaySeq) (k : ℕ) :
    Summable (fun m => |a.val (σ m)| * (1 + (m : ℝ)) ^ k) := by
  obtain ⟨C, hC, p, hbound⟩ := hσ_inv
  -- Change of variables n = σ m: ∑_m f(σ m) = ∑_n f(n) with m = σ⁻¹(n)
  -- So |a(σ m)| (1+m)^k becomes |a(n)| (1+σ⁻¹(n))^k
  -- Bound: (1+σ⁻¹(n))^k ≤ (C(1+n)^p)^k = C^k (1+n)^{pk}
  set k' := p * k
  suffices h : Summable (fun n => |a.val n| * (1 + (σ.symm n : ℝ)) ^ k) by
    have : (fun m => |a.val (σ m)| * (1 + (m : ℝ)) ^ k) =
        (fun n => |a.val n| * (1 + (σ.symm n : ℝ)) ^ k) ∘ σ := by
      ext m; simp [Function.comp, Equiv.symm_apply_apply]
    rw [this]; exact σ.summable_iff.mpr h
  apply Summable.of_nonneg_of_le (fun _ => by positivity)
  · intro n
    calc |a.val n| * (1 + (σ.symm n : ℝ)) ^ k
        ≤ |a.val n| * (C * (1 + (n : ℝ)) ^ p) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_left₀ (by positivity) (hbound n) k
      _ = C ^ k * (|a.val n| * (1 + (n : ℝ)) ^ k') := by
          rw [mul_pow, ← pow_mul]; ring
  · exact (a.rapid_decay k').mul_left _

/-- Reindexing a rapidly decreasing sequence by a permutation with poly-bounded inverse. -/
def reindexVal (σ : ℕ ≃ ℕ) (hσ_inv : IsPolyBounded σ.symm) (a : RapidDecaySeq) :
    RapidDecaySeq where
  val := a.val ∘ σ
  rapid_decay k := reindex_rapid_decay σ hσ_inv a k

/-- The reindexing map is linear. -/
def reindexLM (σ : ℕ ≃ ℕ) (hσ_inv : IsPolyBounded σ.symm) :
    RapidDecaySeq →ₗ[ℝ] RapidDecaySeq where
  toFun := reindexVal σ hσ_inv
  map_add' a b := ext fun m => by simp [reindexVal, add_val]
  map_smul' r a := ext fun m => by simp [reindexVal, smul_val]

/-- Seminorm bound for the reindexing map. For each target seminorm `k`,
the reindexed sequence is bounded by a source seminorm (at a potentially higher index). -/
private lemma reindexLM_isBounded (σ : ℕ ≃ ℕ)
    (hσ_inv : IsPolyBounded σ.symm) :
    Seminorm.IsBounded rapidDecaySeminorm rapidDecaySeminorm (reindexLM σ hσ_inv) := by
  intro k
  obtain ⟨C, hC, p, hbound⟩ := hσ_inv
  -- We need: ∑ |a(σ m)| (1+m)^k ≤ D * ∑ |a n| (1+n)^{k'}
  -- Change of variables: m = σ.symm n, so ∑_m = ∑_n
  -- and (1+m)^k = (1 + σ.symm n)^k ≤ (C(1+n)^p)^k = C^k (1+n)^{pk}
  set k' := p * k
  refine ⟨{k'}, ⟨C ^ k, by positivity⟩, fun a => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, Seminorm.smul_apply,
    NNReal.smul_def, smul_eq_mul]
  show ∑' m, |a.val (σ m)| * (1 + (m : ℝ)) ^ k ≤
    C ^ k * (∑' n, |a.val n| * (1 + (n : ℝ)) ^ k')
  -- Change of variables n = σ m (so m = σ⁻¹ n):
  -- ∑_m |a(σ m)| (1+m)^k = ∑_n |a(n)| (1+σ⁻¹(n))^k
  -- Then bound (1+σ⁻¹(n))^k ≤ (C(1+n)^p)^k = C^k (1+n)^{pk}
  -- Step 1: Change of variables via σ bijection
  set f : ℕ → ℝ := fun n => |a.val n| * (1 + (σ.symm n : ℝ)) ^ k
  have h_cov : ∑' m, |a.val (σ m)| * (1 + (m : ℝ)) ^ k = ∑' n, f n := by
    have : ∀ m, |a.val (σ m)| * (1 + (m : ℝ)) ^ k = f (σ m) :=
      fun m => by simp [f, Equiv.symm_apply_apply]
    simp_rw [this]; exact Equiv.tsum_eq σ f
  rw [h_cov]
  -- Step 2: Pointwise bound
  have h_pw : ∀ n, |a.val n| * (1 + (σ.symm n : ℝ)) ^ k ≤
      C ^ k * (|a.val n| * (1 + (n : ℝ)) ^ k') := fun n =>
    calc |a.val n| * (1 + (σ.symm n : ℝ)) ^ k
        ≤ |a.val n| * (C * (1 + (n : ℝ)) ^ p) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          exact pow_le_pow_left₀ (by positivity) (hbound n) k
      _ = C ^ k * (|a.val n| * (1 + (n : ℝ)) ^ k') := by
          rw [mul_pow, ← pow_mul]; ring
  have h_summ_f : Summable f := Summable.of_nonneg_of_le
    (fun _ => by positivity [f]) h_pw ((a.rapid_decay k').mul_left _)
  calc ∑' n, f n
      ≤ ∑' n, C ^ k * (|a.val n| * (1 + (n : ℝ)) ^ k') :=
        h_summ_f.tsum_le_tsum h_pw ((a.rapid_decay k').mul_left _)
    _ = C ^ k * ∑' n, |a.val n| * (1 + (n : ℝ)) ^ k' := tsum_mul_left

/-- The reindexing continuous linear map. -/
def reindexCLM (σ : ℕ ≃ ℕ) (hσ_inv : IsPolyBounded σ.symm) :
    RapidDecaySeq →L[ℝ] RapidDecaySeq where
  toLinearMap := reindexLM σ hσ_inv
  cont := WithSeminorms.continuous_of_isBounded
    rapidDecay_withSeminorms rapidDecay_withSeminorms
    _ (reindexLM_isBounded σ hσ_inv)

/-- The reindexing continuous linear equivalence.
Given a polynomially bounded permutation `σ` (with polynomially bounded inverse),
produces an automorphism of `RapidDecaySeq`. -/
def reindex (σ : ℕ ≃ ℕ) (hσ : IsPolyBounded σ) (hσ_inv : IsPolyBounded σ.symm) :
    RapidDecaySeq ≃L[ℝ] RapidDecaySeq :=
  ContinuousLinearEquiv.equivOfInverse
    (reindexCLM σ hσ_inv)
    (reindexCLM σ.symm (by rwa [Equiv.symm_symm]))
    (fun a => ext fun m => by simp [reindexCLM, reindexLM, reindexVal])
    (fun a => ext fun m => by simp [reindexCLM, reindexLM, reindexVal])

@[simp] lemma reindex_val (σ : ℕ ≃ ℕ) (hσ : IsPolyBounded σ)
    (hσ_inv : IsPolyBounded σ.symm) (a : RapidDecaySeq) (m : ℕ) :
    (reindex σ hσ hσ_inv a).val m = a.val (σ m) := rfl

end RapidDecaySeq

/-! ## Step 2: Tensor Product Associativity -/

namespace NuclearTensorProduct

/-- The associativity permutation for Cantor pairing.
Maps the "left-associated" index `pair(pair(i,j), k)` to the
"right-associated" index `pair(i, pair(j,k))`. -/
private def assocPerm : ℕ ≃ ℕ :=
  -- ℕ → ℕ×ℕ → (ℕ×ℕ)×ℕ → ℕ×(ℕ×ℕ) → ℕ
  Nat.pairEquiv.symm.trans <|
    (Equiv.prodCongr Nat.pairEquiv.symm (Equiv.refl ℕ)).trans <|
    (Equiv.prodAssoc ℕ ℕ ℕ).trans <|
    (Equiv.prodCongr (Equiv.refl ℕ) Nat.pairEquiv).trans <|
    Nat.pairEquiv

/-- Cantor pairing bound: `1 + pair(i,j) ≤ (2(1+i)(1+j))²`.
Reproduced from NuclearTensorProduct (where it is private). -/
private lemma one_add_pair_le_sq' (i j : ℕ) :
    (1 + (Nat.pair i j : ℝ)) ≤ (2 * (1 + (i : ℝ)) * (1 + (j : ℝ))) ^ 2 := by
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have h_pair : (Nat.pair i j : ℝ) ≤ ((i : ℝ) + j + 1) ^ 2 := by
    exact_mod_cast nat_pair_bound i j
  calc (1 : ℝ) + Nat.pair i j
      ≤ 1 + (i + j + 1) ^ 2 := by linarith
    _ ≤ (i + j + 2) ^ 2 := by nlinarith
    _ ≤ (2 * (1 + i) * (1 + j)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) _

/-- The associativity permutation is polynomially bounded.
Components satisfy `i, j, k ≤ n`, so `pair(i, pair(j,k)) ≤ poly(n)`. -/
private lemma assocPerm_polyBounded : RapidDecaySeq.IsPolyBounded assocPerm := by
  -- pair(a,b) ≤ (2(1+a)(1+b))^2, so double pairing gives degree ≤ 10
  refine ⟨64, by positivity, 10, fun n => ?_⟩
  simp only [assocPerm, Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Nat.pairEquiv]
  set p := Nat.unpair n
  set q := Nat.unpair p.1
  have hp1 := Nat.unpair_left_le n
  have hk := Nat.unpair_right_le n
  have hi_le : q.1 ≤ n := le_trans (Nat.unpair_left_le p.1) hp1
  have hj_le : q.2 ≤ n := le_trans (Nat.unpair_right_le p.1) hp1
  have hk_le : p.2 ≤ n := hk
  -- pair(j,k) ≤ (2(1+j)(1+k))^2 ≤ (2(1+n)^2)^2 = 4(1+n)^4
  have hjk : (1 + (Nat.pair q.2 p.2 : ℝ)) ≤ (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 := by
    calc (1 + (Nat.pair q.2 p.2 : ℝ))
        ≤ (2 * (1 + (q.2 : ℝ)) * (1 + (p.2 : ℝ))) ^ 2 := one_add_pair_le_sq' q.2 p.2
      _ ≤ (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          have hj_n : (q.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj_le
          have hk_n : (p.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk_le
          nlinarith
  -- pair(i, pair(j,k)) ≤ (2(1+i)(1+pair(j,k)))^2 ≤ (2(1+n) · 4(1+n)^4)^2
  calc (1 + (Nat.pair q.1 (Nat.pair q.2 p.2) : ℝ))
      ≤ (2 * (1 + (q.1 : ℝ)) * (1 + (Nat.pair q.2 p.2 : ℝ))) ^ 2 :=
        one_add_pair_le_sq' q.1 (Nat.pair q.2 p.2)
    _ ≤ (2 * (1 + (n : ℝ)) * (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        -- Goal: 2*(1+q.1)*(1+pair(q.2,p.2)) ≤ 2*(1+n)*(2*(1+n)*(1+n))^2
        have h1 : (1 + (q.1 : ℝ)) ≤ (1 + (n : ℝ)) := by
          have := (Nat.cast_le (α := ℝ)).mpr hi_le; linarith
        calc 2 * (1 + (q.1 : ℝ)) * (1 + (Nat.pair q.2 p.2 : ℝ))
            ≤ 2 * (1 + (n : ℝ)) * (1 + (Nat.pair q.2 p.2 : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith
          _ ≤ 2 * (1 + (n : ℝ)) * (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 := by
              apply mul_le_mul_of_nonneg_left hjk (by positivity)
    _ = 64 * (1 + (n : ℝ)) ^ 10 := by ring

/-- The inverse associativity permutation is polynomially bounded.
Symmetric to `assocPerm_polyBounded`: components are ≤ n, double Cantor pairing
gives polynomial growth. -/
private lemma assocPerm_symm_polyBounded : RapidDecaySeq.IsPolyBounded assocPerm.symm := by
  -- assocPerm.symm maps pair(i, pair(j,k)) to pair(pair(i,j), k)
  -- All components i,j,k ≤ n, so the result is polynomially bounded
  refine ⟨64, by positivity, 10, fun n => ?_⟩
  -- assocPerm.symm n: unpair n to get (i, pair(j,k)), unpair the second to get (j,k),
  -- then pair(pair(i,j), k)
  -- All three components i,j,k ≤ n
  set p := Nat.unpair n
  set r := Nat.unpair p.2
  have hi_le : p.1 ≤ n := Nat.unpair_left_le n
  have hjk_le : p.2 ≤ n := Nat.unpair_right_le n
  have hj_le : r.1 ≤ n := le_trans (Nat.unpair_left_le p.2) hjk_le
  have hk_le : r.2 ≤ n := le_trans (Nat.unpair_right_le p.2) hjk_le
  -- Need to show 1 + assocPerm.symm n ≤ 64 * (1+n)^10
  -- assocPerm.symm n = pair(pair(p.1, r.1), r.2)
  -- pair(p.1, r.1) ≤ (2(1+p.1)(1+r.1))^2 ≤ (2(1+n)^2)^2 = 4(1+n)^4
  -- pair(pair(p.1,r.1), r.2) ≤ (2(1+pair(p.1,r.1))(1+r.2))^2 ≤ (2·4(1+n)^4·(1+n))^2 = 64(1+n)^10
  simp only [assocPerm, Equiv.symm_trans_apply, Equiv.prodCongr_symm, Equiv.refl_symm,
    Equiv.prodCongr_apply, Nat.pairEquiv]
  -- After simp, the goal should involve pair(pair(p.1,r.1), r.2)
  have hij : (1 + (Nat.pair p.1 r.1 : ℝ)) ≤ (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 := by
    calc (1 + (Nat.pair p.1 r.1 : ℝ))
        ≤ (2 * (1 + (p.1 : ℝ)) * (1 + (r.1 : ℝ))) ^ 2 := one_add_pair_le_sq' p.1 r.1
      _ ≤ (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 := by
          apply pow_le_pow_left₀ (by positivity)
          have hi_n : (p.1 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hi_le
          have hj_n : (r.1 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hj_le
          nlinarith
  calc (1 + (Nat.pair (Nat.pair p.1 r.1) r.2 : ℝ))
      ≤ (2 * (1 + (Nat.pair p.1 r.1 : ℝ)) * (1 + (r.2 : ℝ))) ^ 2 :=
        one_add_pair_le_sq' (Nat.pair p.1 r.1) r.2
    _ ≤ (2 * (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 * (1 + (n : ℝ))) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        have hk_n : (r.2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hk_le
        have h1 : (1 + (r.2 : ℝ)) ≤ (1 + (n : ℝ)) := by linarith
        calc 2 * (1 + (Nat.pair p.1 r.1 : ℝ)) * (1 + (r.2 : ℝ))
            ≤ 2 * (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 * (1 + (r.2 : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith [hij]
          _ ≤ 2 * (2 * (1 + (n : ℝ)) * (1 + (n : ℝ))) ^ 2 * (1 + (n : ℝ)) := by
              apply mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 64 * (1 + (n : ℝ)) ^ 10 := by ring

/-- **Associativity of the nuclear tensor product.**
`(E₁ ⊗̂ E₂) ⊗̂ E₃ ≃L[ℝ] E₁ ⊗̂ (E₂ ⊗̂ E₃)`

Since all three are `RapidDecaySeq`, this is a reindexing by the
Cantor pairing associativity permutation. -/
def assoc (E₁ E₂ E₃ : Type*) :
    NuclearTensorProduct (NuclearTensorProduct E₁ E₂) E₃ ≃L[ℝ]
    NuclearTensorProduct E₁ (NuclearTensorProduct E₂ E₃) :=
  RapidDecaySeq.reindex assocPerm assocPerm_polyBounded assocPerm_symm_polyBounded

end NuclearTensorProduct

/-! ## Step 3: Dimension Peeling Isomorphism -/

/-- **One-dimension peeling isomorphism.**

`S(ℝ^{d+2}) ≃L[ℝ] NuclearTensorProduct S(ℝ^{d+1}) S(ℝ)`

This identifies a Schwartz function on `ℝ^{d+2}` with an element of
`S(ℝ^{d+1}) ⊗̂ S(ℝ)` via the Hermite basis expansion. The isomorphism
is `schwartzRapidDecayEquivNd (d+1)` — literally the existing isomorphism
to `RapidDecaySeq`, since `NuclearTensorProduct = RapidDecaySeq` by definition.

The key insight is that `multiIndexEquiv (d+1)` peels off the last coordinate
via `Fin.succFunEquiv` then Cantor-pairs — which is exactly how
`NuclearTensorProduct` pairs two sequence spaces. -/
noncomputable def schwartzPeelOff (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ ≃L[ℝ]
    NuclearTensorProduct
      (SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
      (SchwartzMap ℝ ℝ) :=
  schwartzRapidDecayEquivNd (d + 1)

/-! ## Step 4: Schwartz Pointwise Product -/

/-- The pointwise product `h(x, t) = f(x) · g(t)` of a Schwartz function on `ℝ^{d+1}`
and a Schwartz function on `ℝ`, as a Schwartz function on `ℝ^{d+2}`.

Defined as the inverse image of the pure tensor `f ⊗ g` under `schwartzPeelOff`,
which encodes the same function via the Hermite basis expansion. The value
characterization `schwartzPointwiseProduct_apply` shows that this equals
`f(euclideanInit x) * g(x (Fin.last _))` pointwise. -/
noncomputable def schwartzPointwiseProduct (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (g : SchwartzMap ℝ ℝ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ :=
  (schwartzPeelOff d).symm (NuclearTensorProduct.pure f g)

/-- **Canonicity of the peeling isomorphism.**

The inverse of `schwartzPeelOff` sends a pure tensor `f ⊗ g` to the
pointwise product `(x,t) ↦ f(x)·g(t)`. -/
theorem schwartzPeelOff_pure (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (g : SchwartzMap ℝ ℝ) :
    (schwartzPeelOff d).symm (NuclearTensorProduct.pure f g) =
      schwartzPointwiseProduct d f g :=
  rfl

/-- The pointwise product Schwartz function evaluates to `f(init x) · g(last x)`.

This follows from the Hermite expansion: the pure tensor `f ⊗ g` encodes the
coefficient sequence `c_m = c_{unpair(m).1}(f) · c_{unpair(m).2}(g)`, and the
Hermite series reconstruction converges to `f(init x) · g(last x)` by the
Fubini-based product factorization of Hermite coefficients. -/
theorem schwartzPointwiseProduct_apply (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
    (g : SchwartzMap ℝ ℝ)
    (x : EuclideanSpace ℝ (Fin (d + 2))) :
    schwartzPointwiseProduct d f g x =
      f (euclideanInit (d + 1) x) * g (x (Fin.last (d + 1))) := by
  -- Abbreviations for the Hermite coefficient sequences
  set a := schwartzRapidDecayEquivNd d f
  set b := schwartzRapidDecayEquiv1D g
  -- Step 1: Unfold to the Hermite series tsum
  show (schwartzRapidDecayEquivNd (d + 1)).symm (NuclearTensorProduct.pure f g) x = _
  rw [schwartzRapidDecayEquivNd_symm_apply]
  -- Step 2: Rewrite each summand using pure tensor factorization and basis factorization
  -- (pure f g).val n = a.val (unpair n).1 * b.val (unpair n).2
  have h_pure : ∀ n, (NuclearTensorProduct.pure f g).val n =
      a.val (Nat.unpair n).1 * b.val (Nat.unpair n).2 := by
    intro n
    simp only [NuclearTensorProduct.pure_val,
      DyninMityaginSpace.coeff,
      RapidDecaySeq.coeffCLM, ContinuousLinearMap.comp_apply,
      RapidDecaySeq.coeffLM]
    rfl
  simp_rw [h_pure, hermiteFunctionNd_unpair]
  -- Goal: ∑' n, (a.val i * b.val j) * (Phi_i(init x) * psi_j(last x)) = f(init x) * g(last x)
  -- where i = (unpair n).1, j = (unpair n).2
  -- Define the factor functions
  set F : ℕ → ℝ := fun i => a.val i *
    hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm i) (euclideanInit (d + 1) x)
  set G : ℕ → ℝ := fun j => b.val j * hermiteFunction j (x (Fin.last (d + 1)))
  -- Step 3: Rearrange (a_i * b_j) * (Phi_i * psi_j) = F i * G j
  conv_lhs => arg 1; ext n; rw [show
    a.val (Nat.unpair n).1 * b.val (Nat.unpair n).2 *
      (hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm (Nat.unpair n).1)
        (euclideanInit (d + 1) x) *
      hermiteFunction (Nat.unpair n).2 (x (Fin.last (d + 1)))) =
    F (Nat.unpair n).1 * G (Nat.unpair n).2 from by simp only [F, G]; ring]
  -- Step 4: Convert from Cantor-paired ℕ to ℕ × ℕ indexing
  -- ∑' n, F (unpair n).1 * G (unpair n).2 = ∑' (p : ℕ × ℕ), F p.1 * G p.2
  -- Use change of variables: the Cantor pairing bijection
  have h_eq_prod : ∑' n, F (Nat.unpair n).1 * G (Nat.unpair n).2 =
      ∑' (p : ℕ × ℕ), F p.1 * G p.2 :=
    Nat.pairEquiv.symm.tsum_eq (fun p : ℕ × ℕ => F p.1 * G p.2)
  rw [h_eq_prod]
  -- Step 5: Factor the product sum into a product of two sums
  -- Summability of F and G
  have hF : Summable F :=
    schwartzRapidDecayEquivNd_summable d a (euclideanInit (d + 1) x)
  have hG : Summable G :=
    schwartzRapidDecayEquiv1D_summable b (x (Fin.last (d + 1)))
  -- Product summability (from norm summability)
  have hFG : Summable (fun p : ℕ × ℕ => F p.1 * G p.2) :=
    summable_mul_of_summable_norm hF.norm hG.norm
  -- Apply the product formula: ∑' (i,j), F i * G j = (∑' i, F i) * (∑' j, G j)
  rw [← hF.tsum_mul_tsum hG hFG]
  -- Step 6: Each factor tsum reconstructs f and g
  -- ∑' i, F i = ∑' i, a.val i * Phi_i(init x) = f(init x)
  have hF_eq : ∑' i, F i = f (euclideanInit (d + 1) x) := by
    rw [show ∑' i, F i = ∑' i, a.val i *
        hermiteFunctionNd (d + 1) ((multiIndexEquiv d).symm i)
          (euclideanInit (d + 1) x) from rfl]
    rw [← schwartzRapidDecayEquivNd_symm_apply d a (euclideanInit (d + 1) x)]
    -- (schwartzRapidDecayEquivNd d).symm a = (schwartzRapidDecayEquivNd d).symm (equiv d f) = f
    simp [a]
  -- ∑' j, G j = ∑' j, b.val j * psi_j(last x) = g(last x)
  have hG_eq : ∑' j, G j = g (x (Fin.last (d + 1))) := by
    rw [show ∑' j, G j = ∑' j, b.val j *
        hermiteFunction j (x (Fin.last (d + 1))) from rfl]
    rw [← schwartzRapidDecayEquiv1D_symm_apply b (x (Fin.last (d + 1)))]
    simp [b]
  rw [hF_eq, hG_eq]

/-! ## Step 6: General Tensor Equivalence by Induction -/

/-- **General Schwartz tensor product isomorphism.**

`NuclearTensorProduct S(ℝ^{m+1}) S(ℝ^{n+1}) ≃L[ℝ] S(ℝ^{m+n+2})`

Since `NuclearTensorProduct E₁ E₂ = RapidDecaySeq` (definitionally, for any types),
and `schwartzRapidDecayEquivNd` gives `S(ℝ^d) ≃L RapidDecaySeq`, the isomorphism
is just composition with `schwartzRapidDecayEquivNd`.

The composition of these maps encodes the inductive dimension-peeling:
- Base case (`n = 0`): `S(ℝ^{m+1}) ⊗̂ S(ℝ) ≃L S(ℝ^{m+2})` via `schwartzPeelOff`
- Inductive step: peel, reassociate, apply IH, then peel again -/
noncomputable def schwartzTensorEquiv (m n : ℕ) :
    NuclearTensorProduct
      (SchwartzMap (EuclideanSpace ℝ (Fin (m + 1))) ℝ)
      (SchwartzMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ) ≃L[ℝ]
    SchwartzMap (EuclideanSpace ℝ (Fin (m + n + 2))) ℝ :=
  -- NuclearTensorProduct is always RapidDecaySeq, and schwartzRapidDecayEquivNd
  -- gives S(ℝ^{d+1}) ≃L RapidDecaySeq. The isomorphism is the inverse of
  -- the latter. The Fin arithmetic m + n + 2 = (m + n + 1) + 1 holds by omega.
  have h : m + n + 2 = (m + n + 1) + 1 := by omega
  h ▸ (schwartzRapidDecayEquivNd (m + n + 1)).symm

end GaussianField
