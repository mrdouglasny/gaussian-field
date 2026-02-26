/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rapidly Decaying Functions on ℤ^d

Defines `RapidDecayLattice d`, the space of rapidly decaying functions on ℤ^d,
and establishes its DyninMityaginSpace structure via a continuous linear
equivalence with `RapidDecaySeq`.

## Main definitions

- `RapidDecayLattice d` — rapidly decaying functions on ℤ^d
- `latticeRapidDecaySeminorm d k` — seminorm: `∑_x |f(x)| (1+|x|)^k`
- `latticeEnum d` — shell enumeration `ℤ^d ≃ ℕ`
- `latticeRapidDecayEquiv d` — CLE to `RapidDecaySeq`
- `DyninMityaginSpace` instance via `ofRapidDecayEquiv`
- `HasPointEval` instance

## Key difficulty

The CLE proof needs polynomially bounded reindexing:
`latticeNorm (latticeEnum.symm m) ≤ C · (1+m)^p` and
`latticeEnum x ≤ C · (1+|x|)^q` for some exponents `p, q`.
For `d = 0`, `(Fin 0 → ℤ)` is a singleton and should be handled separately as a
one-dimensional case rather than via an `ℤ^d ≃ ℕ` reindexing.

## References

- Dynin-Mityagin, via the general transfer constructor `ofRapidDecayEquiv`
-/

import Lattice.Sites
import Nuclear.NuclearTensorProduct
import Nuclear.PointEval
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic

noncomputable section

namespace GaussianField

/-! ## Rapidly Decaying Lattice Functions -/

/-- A rapidly decaying function on ℤ^d: `val : (Fin d → ℤ) → ℝ` such that
`∑_x |val x| · (1 + latticeNorm x)^k` converges for all `k : ℕ`. -/
structure RapidDecayLattice (d : ℕ) where
  val : (Fin d → ℤ) → ℝ
  rapid_decay : ∀ k : ℕ, Summable (fun x => |val x| * (1 + latticeNorm x) ^ k)

namespace RapidDecayLattice

variable {d : ℕ}
set_option maxHeartbeats 1200000

@[ext]
theorem ext {a b : RapidDecayLattice d} (h : ∀ x, a.val x = b.val x) : a = b := by
  cases a; cases b; congr 1; exact funext h

/-! ### Weight function lemmas -/

theorem weight_pos (x : Fin d → ℤ) (k : ℕ) : (0 : ℝ) < (1 + latticeNorm x) ^ k := by
  apply pow_pos
  linarith [latticeNorm_nonneg x]

theorem weight_nonneg (x : Fin d → ℤ) (k : ℕ) : (0 : ℝ) ≤ (1 + latticeNorm x) ^ k :=
  le_of_lt (weight_pos x k)

/-! ### Algebraic structure -/

instance instZero : Zero (RapidDecayLattice d) where
  zero := ⟨0, fun k => by simp [summable_zero]⟩

@[simp] theorem zero_val (x : Fin d → ℤ) : (0 : RapidDecayLattice d).val x = 0 := rfl

instance instAdd : Add (RapidDecayLattice d) where
  add a b := ⟨a.val + b.val, fun k => by
    apply Summable.of_nonneg_of_le
    · intro x; exact mul_nonneg (abs_nonneg _) (weight_nonneg x k)
    · intro x; simp only [Pi.add_apply]
      calc |a.val x + b.val x| * (1 + latticeNorm x) ^ k
          ≤ (|a.val x| + |b.val x|) * (1 + latticeNorm x) ^ k :=
            mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg x k)
        _ = |a.val x| * (1 + latticeNorm x) ^ k +
            |b.val x| * (1 + latticeNorm x) ^ k := add_mul _ _ _
    · exact (a.rapid_decay k).add (b.rapid_decay k)⟩

@[simp] theorem add_val (a b : RapidDecayLattice d) (x : Fin d → ℤ) :
    (a + b).val x = a.val x + b.val x := rfl

instance instNeg : Neg (RapidDecayLattice d) where
  neg a := ⟨fun x => -a.val x, fun k => by
    simp only [abs_neg]; exact a.rapid_decay k⟩

@[simp] theorem neg_val (a : RapidDecayLattice d) (x : Fin d → ℤ) :
    (-a).val x = -a.val x := rfl

instance instSMul : SMul ℝ (RapidDecayLattice d) where
  smul r a := ⟨fun x => r * a.val x, fun k => by
    have h : (fun x => |r * a.val x| * (1 + latticeNorm x) ^ k) =
             fun x => |r| * (|a.val x| * (1 + latticeNorm x) ^ k) := by
      ext x; rw [abs_mul, mul_assoc]
    rw [h]
    exact (a.rapid_decay k).const_smul |r|⟩

@[simp] theorem smul_val (r : ℝ) (a : RapidDecayLattice d) (x : Fin d → ℤ) :
    (r • a).val x = r * a.val x := rfl

instance instAddCommGroup : AddCommGroup (RapidDecayLattice d) where
  add_assoc a b c := ext fun x => add_assoc _ _ _
  zero_add a := ext fun x => zero_add _
  add_zero a := ext fun x => add_zero _
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := ext fun x => neg_add_cancel _
  add_comm a b := ext fun x => add_comm _ _

instance instModule : Module ℝ (RapidDecayLattice d) where
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/-! ### Seminorm family -/

/-- The k-th seminorm on rapidly decaying lattice functions:
`∑_x |f(x)| · (1 + latticeNorm x)^k`. -/
def latticeRapidDecaySeminorm (d : ℕ) (k : ℕ) :
    Seminorm ℝ (RapidDecayLattice d) where
  toFun a := ∑' x, |a.val x| * (1 + latticeNorm x) ^ k
  map_zero' := by simp [zero_val, tsum_zero]
  add_le' a b := by
    calc ∑' x, |(a + b).val x| * (1 + latticeNorm x) ^ k
        ≤ ∑' x, (|a.val x| * (1 + latticeNorm x) ^ k +
                  |b.val x| * (1 + latticeNorm x) ^ k) := by
          exact ((a + b).rapid_decay k).tsum_le_tsum
            (fun x => by simp only [add_val]
                         calc |a.val x + b.val x| * (1 + latticeNorm x) ^ k
                             ≤ (|a.val x| + |b.val x|) * (1 + latticeNorm x) ^ k :=
                               mul_le_mul_of_nonneg_right (abs_add_le _ _) (weight_nonneg x k)
                           _ = _ := add_mul _ _ _)
            ((a.rapid_decay k).add (b.rapid_decay k))
      _ = ∑' x, |a.val x| * (1 + latticeNorm x) ^ k +
          ∑' x, |b.val x| * (1 + latticeNorm x) ^ k :=
          (a.rapid_decay k).tsum_add (b.rapid_decay k)
  neg' a := by
    congr 1; ext x; rw [neg_val, abs_neg]
  smul' r a := by
    show ∑' x, |r * a.val x| * (1 + latticeNorm x) ^ k =
      ‖r‖ * ∑' x, |a.val x| * (1 + latticeNorm x) ^ k
    simp_rw [abs_mul, Real.norm_eq_abs, mul_assoc]
    exact tsum_mul_left

/-! ### Topology from seminorms -/

instance instTopologicalSpace : TopologicalSpace (RapidDecayLattice d) :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) (latticeRapidDecaySeminorm d)).topology

theorem lattice_withSeminorms :
    WithSeminorms (latticeRapidDecaySeminorm d :
      ℕ → Seminorm ℝ (RapidDecayLattice d)) :=
  ⟨rfl⟩

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (RapidDecayLattice d) :=
  lattice_withSeminorms.topologicalAddGroup

instance instContinuousSMul : ContinuousSMul ℝ (RapidDecayLattice d) :=
  lattice_withSeminorms.continuousSMul

/-! ### Enumeration of ℤ^d

We need an explicit bijection `(Fin d → ℤ) ≃ ℕ` with polynomial norm growth.
A shell enumeration (ordered by ℓ¹ norm, ties broken lexicographically) works.

Key property: both directions are polynomially bounded:
`latticeNorm (enum.symm m) ≤ C · (1+m)^p` and
`enum(x) ≤ C · (1+|x|)^q`.

The bijection is constructed via iterated Cantor pairing (`Denumerable.eqv`)
and coordinate peeling (`Fin.succFunEquiv`). -/

/-- Cantor-pairing enumeration of ℤ^{d+1}: bijection with ℕ via iterated
pairing. Constructed using `Fin.succFunEquiv` (peeling off one coordinate)
and `Denumerable.eqv` (encoding products and ℤ as ℕ). -/
private def latticeEnumSucc : (d : ℕ) → (Fin (d + 1) → ℤ) ≃ ℕ
  | 0 => (Equiv.funUnique (Fin 1) ℤ).trans (Denumerable.eqv ℤ)
  | d + 1 =>
    (Fin.succFunEquiv ℤ (d + 1)).trans
      (((latticeEnumSucc d).prodCongr (Denumerable.eqv ℤ)).trans
        (Denumerable.eqv (ℕ × ℕ)))

/-- Shell enumeration of ℤ^d: bijection with ℕ (requires `d ≥ 1`).
For `d = 0`, `(Fin 0 → ℤ)` is a singleton, so no such bijection exists. -/
def latticeEnum (d : ℕ) [NeZero d] : (Fin d → ℤ) ≃ ℕ := by
  cases d with
  | zero =>
      exfalso
      exact (NeZero.ne (0 : ℕ)) rfl
  | succ d =>
      exact latticeEnumSucc d

/-- Quantitative bound for the integer decoder used by `Equiv.intEquivNat`. -/
private lemma natAbs_intEquivNat_symm_le_succ (n : ℕ) :
    Int.natAbs (Equiv.intEquivNat.symm n) ≤ n + 1 := by
  change Int.natAbs (Sum.elim Int.ofNat Int.negSucc
    (if n.bodd = true then Sum.inr n.div2 else Sum.inl n.div2)) ≤ n + 1
  by_cases h : n.bodd = true
  · rw [if_pos h]
    simp
    have hd : n.div2 ≤ n := by
      have hb := Nat.bodd_add_div2 n
      omega
    omega
  · rw [if_neg h]
    simp
    have hd : n.div2 ≤ n := by
      have hb := Nat.bodd_add_div2 n
      omega
    omega

/-- Real-valued form of `natAbs_intEquivNat_symm_le_succ`. -/
private lemma abs_intEquivNat_symm_cast_le_succ (n : ℕ) :
    |((Equiv.intEquivNat.symm n : ℤ) : ℝ)| ≤ n + 1 := by
  let z : ℤ := Equiv.intEquivNat.symm n
  have hnat : Int.natAbs z ≤ n + 1 := by
    simpa [z] using natAbs_intEquivNat_symm_le_succ n
  have hcastZ : ((Int.natAbs z : ℕ) : ℤ) ≤ (n + 1 : ℤ) := by
    exact_mod_cast hnat
  have habseq : (|z| : ℤ) = ((Int.natAbs z : ℕ) : ℤ) := Int.abs_eq_natAbs z
  have habs : (|z| : ℤ) ≤ (n + 1 : ℤ) := habseq ▸ hcastZ
  have hreal : ((|z| : ℤ) : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast habs
  have hcastabs : ((|z| : ℤ) : ℝ) = |(z : ℝ)| := Int.cast_abs
  calc
    |(z : ℝ)| = ((|z| : ℤ) : ℝ) := hcastabs.symm
    _ ≤ (n + 1 : ℝ) := hreal

/-- Forward growth bound for `Equiv.intEquivNat`. -/
private lemma intEquivNat_le_two_natAbs_add_one (z : ℤ) :
    Equiv.intEquivNat z ≤ 2 * Int.natAbs z + 1 := by
  cases z with
  | ofNat n =>
      change 2 * n ≤ 2 * n + 1
      omega
  | negSucc n =>
      change 2 * n + 1 ≤ 2 * (n + 1) + 1
      omega

/-- Coordinate-wise absolute values are bounded by the ℓ¹ norm. -/
private lemma abs_coord_le_latticeNorm {d : ℕ} (x : Fin d → ℤ) (i : Fin d) :
    |(x i : ℝ)| ≤ latticeNorm x := by
  unfold latticeNorm
  exact Finset.single_le_sum (fun j _ => abs_nonneg ((x j : ℤ) : ℝ)) (by simp)

/-- Real bound for `Nat.pair`: quadratic in the total size of inputs. -/
private lemma pair_cast_le_square (a b : ℕ) :
    (Nat.pair a b : ℝ) ≤ (a + b + 1 : ℝ) ^ 2 := by
  have hlt : Nat.pair a b < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
  have hle1 : Nat.pair a b ≤ (max a b + 1) ^ 2 := Nat.le_of_lt hlt
  have hmax : max a b ≤ a + b := by
    exact max_le (Nat.le_add_right a b) (Nat.le_add_left b a)
  have hle2 : (max a b + 1) ^ 2 ≤ (a + b + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (Nat.succ_le_succ hmax) 2
  exact_mod_cast (le_trans hle1 hle2)

/-- Real-valued forward growth bound for integer encoding. -/
private lemma intEquivNat_cast_le_three_mul (z : ℤ) :
    (Equiv.intEquivNat z : ℝ) ≤ 3 * (1 + |(z : ℝ)|) := by
  have hnat : Equiv.intEquivNat z ≤ 2 * Int.natAbs z + 1 :=
    intEquivNat_le_two_natAbs_add_one z
  have hreal_nat : (Equiv.intEquivNat z : ℝ) ≤ (2 * Int.natAbs z + 1 : ℕ) := by
    exact_mod_cast hnat
  have habs : (Int.natAbs z : ℝ) = |(z : ℝ)| := by
    calc
      (Int.natAbs z : ℝ) = ((Int.natAbs z : ℕ) : ℤ) := by norm_num
      _ = (|z| : ℤ) := by rw [Int.abs_eq_natAbs]
      _ = |(z : ℝ)| := by exact_mod_cast (Int.cast_abs (a := z))
  calc
    (Equiv.intEquivNat z : ℝ) ≤ (2 * Int.natAbs z + 1 : ℕ) := hreal_nat
    _ = 2 * |(z : ℝ)| + 1 := by norm_num [habs]
    _ ≤ 3 * (1 + |(z : ℝ)|) := by nlinarith

/-- Splitting formula for the ℓ¹ norm under `Fin.succFunEquiv`. -/
private lemma latticeNorm_succFunEquiv_symm (d : ℕ) (p : (Fin d → ℤ) × ℤ) :
    latticeNorm ((Fin.succFunEquiv ℤ d).symm p) =
      latticeNorm p.1 + |(p.2 : ℝ)| := by
  rcases p with ⟨x, z⟩
  simp [latticeNorm, Fin.succFunEquiv, Fin.sum_univ_add]

/-- Inverse polynomial growth for the recursively defined enumeration. -/
private theorem latticeEnumSucc_norm_bound :
    ∀ d : ℕ, ∃ C > (0 : ℝ), ∃ p : ℕ, ∀ m : ℕ,
      latticeNorm ((latticeEnumSucc d).symm m) ≤ C * (1 + (m : ℝ)) ^ p
  | 0 => by
      refine ⟨1, by positivity, 1, ?_⟩
      intro m
      have h := abs_intEquivNat_symm_cast_le_succ m
      simpa [latticeEnumSucc, latticeNorm, add_comm, add_left_comm, add_assoc] using h
  | d + 1 => by
      rcases latticeEnumSucc_norm_bound d with ⟨C, hC, p, hp⟩
      refine ⟨C + 1, by positivity, p + 1, ?_⟩
      intro m
      have hm_one : (1 : ℝ) ≤ 1 + (m : ℝ) := by
        have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast (Nat.zero_le m)
        linarith
      have hleft_nat : (Nat.unpair m).1 ≤ m := Nat.unpair_left_le m
      have hleft : ((Nat.unpair m).1 : ℝ) ≤ m := by exact_mod_cast hleft_nat
      have hpow_left :
          (1 + ((Nat.unpair m).1 : ℝ)) ^ p ≤ (1 + (m : ℝ)) ^ p := by
        exact pow_le_pow_left₀ (by linarith) (by linarith [hleft]) p
      have hpoly_left :
          C * (1 + ((Nat.unpair m).1 : ℝ)) ^ p ≤ C * (1 + (m : ℝ)) ^ p := by
        exact mul_le_mul_of_nonneg_left hpow_left (le_of_lt hC)
      have hpoly_right :
          |((Equiv.intEquivNat.symm (Nat.unpair m).2 : ℤ) : ℝ)| ≤ 1 + (m : ℝ) := by
        have h := abs_intEquivNat_symm_cast_le_succ (Nat.unpair m).2
        have hright_nat : (Nat.unpair m).2 ≤ m := Nat.unpair_right_le m
        have hright : ((Nat.unpair m).2 : ℝ) ≤ m := by exact_mod_cast hright_nat
        linarith
      have hpow_succ :
          (1 + (m : ℝ)) ^ p ≤ (1 + (m : ℝ)) ^ (p + 1) := by
        calc
          (1 + (m : ℝ)) ^ p ≤ (1 + (m : ℝ)) ^ p * (1 + (m : ℝ)) := by
            exact le_mul_of_one_le_right (by positivity) hm_one
          _ = (1 + (m : ℝ)) ^ (p + 1) := by ring_nf
      have hpow_one :
          (1 + (m : ℝ)) ≤ (1 + (m : ℝ)) ^ (p + 1) := by
        calc
          (1 + (m : ℝ)) ≤ (1 + (m : ℝ)) * (1 + (m : ℝ)) ^ p := by
            exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hm_one)
          _ = (1 + (m : ℝ)) ^ (p + 1) := by ring_nf
      have hsum :
          C * (1 + (m : ℝ)) ^ p + (1 + (m : ℝ))
            ≤ (C + 1) * (1 + (m : ℝ)) ^ (p + 1) := by
        calc
          C * (1 + (m : ℝ)) ^ p + (1 + (m : ℝ))
              ≤ C * (1 + (m : ℝ)) ^ (p + 1) + (1 + (m : ℝ)) ^ (p + 1) := by
                  gcongr
          _ = (C + 1) * (1 + (m : ℝ)) ^ (p + 1) := by ring
      have hpair : (Denumerable.eqv (ℕ × ℕ)).symm m = Nat.unpair m := rfl
      have hint :
          (Denumerable.eqv ℤ).symm ((Denumerable.eqv (ℕ × ℕ)).symm m).2 =
            Equiv.intEquivNat.symm ((Denumerable.eqv (ℕ × ℕ)).symm m).2 := rfl
      calc
        latticeNorm ((latticeEnumSucc (d + 1)).symm m)
            = latticeNorm ((latticeEnumSucc d).symm ((Denumerable.eqv (ℕ × ℕ)).symm m).1) +
              |((Equiv.intEquivNat.symm ((Denumerable.eqv (ℕ × ℕ)).symm m).2 : ℤ) : ℝ)| := by
                simp [latticeEnumSucc, latticeNorm_succFunEquiv_symm, hint]
        _ = latticeNorm ((latticeEnumSucc d).symm (Nat.unpair m).1) +
              |((Equiv.intEquivNat.symm (Nat.unpair m).2 : ℤ) : ℝ)| := by
                simp [hpair]
        _ ≤ C * (1 + ((Nat.unpair m).1 : ℝ)) ^ p +
              |((Equiv.intEquivNat.symm (Nat.unpair m).2 : ℤ) : ℝ)| := by
                gcongr
                exact hp (Nat.unpair m).1
        _ ≤ C * (1 + ((Nat.unpair m).1 : ℝ)) ^ p + (1 + (m : ℝ)) := by
                linarith [hpoly_right]
        _ ≤ C * (1 + (m : ℝ)) ^ p + (1 + (m : ℝ)) := by
              gcongr
        _ ≤ (C + 1) * (1 + (m : ℝ)) ^ (p + 1) := hsum

/-- The enumeration has polynomial inverse growth: the m-th point has
ℓ¹ norm bounded by `C * (1+m)^p` for some `p`. -/
theorem latticeEnum_norm_bound (d : ℕ) [NeZero d] :
    ∃ C > (0 : ℝ), ∃ p : ℕ, ∀ m : ℕ,
    latticeNorm ((latticeEnum d).symm m) ≤ C * (1 + (m : ℝ)) ^ p := by
  cases d with
  | zero =>
      exfalso
      exact (NeZero.ne (0 : ℕ)) rfl
  | succ d =>
      simpa [latticeEnum] using latticeEnumSucc_norm_bound d

/-- Converse polynomial bound: points with small norm have polynomially small
index. -/
private theorem latticeEnumSucc_index_bound :
    ∀ d : ℕ, ∃ C > (0 : ℝ), ∃ q : ℕ, ∀ x : Fin (d + 1) → ℤ,
      (latticeEnumSucc d x : ℝ) ≤ C * (1 + latticeNorm x) ^ q
  | 0 => by
      refine ⟨3, by positivity, 1, ?_⟩
      intro x
      have hx : latticeNorm x = |(x 0 : ℝ)| := by
        simp [latticeNorm]
      have h0 : (latticeEnumSucc 0 x : ℝ) ≤ 3 * (1 + |(x 0 : ℝ)|) := by
        simpa [latticeEnumSucc] using intEquivNat_cast_le_three_mul (x 0)
      simpa [hx, pow_one, mul_assoc, mul_left_comm, mul_comm] using h0
  | d + 1 => by
      rcases latticeEnumSucc_index_bound d with ⟨C, hC, q, hq⟩
      refine ⟨(C + 4) ^ 2, by positivity, 2 * (q + 1), ?_⟩
      intro x
      let p : (Fin (d + 1) → ℤ) × ℤ := Fin.succFunEquiv ℤ (d + 1) x
      have hsplit : latticeNorm x = latticeNorm p.1 + |(p.2 : ℝ)| := by
        have hp : (Fin.succFunEquiv ℤ (d + 1)).symm p = x := by
          simpa [p] using (Fin.succFunEquiv ℤ (d + 1)).symm_apply_apply x
        calc
          latticeNorm x = latticeNorm ((Fin.succFunEquiv ℤ (d + 1)).symm p) := by
            simp [hp]
          _ = latticeNorm p.1 + |(p.2 : ℝ)| :=
            latticeNorm_succFunEquiv_symm (d + 1) p
      have hp1_le : latticeNorm p.1 ≤ latticeNorm x := by
        have habs : (0 : ℝ) ≤ |(p.2 : ℝ)| := abs_nonneg _
        linarith
      have hp2abs_le : |(p.2 : ℝ)| ≤ latticeNorm x := by
        have hp1_nonneg : (0 : ℝ) ≤ latticeNorm p.1 := latticeNorm_nonneg p.1
        linarith
      have hA_one : (1 : ℝ) ≤ 1 + latticeNorm x := by
        linarith [latticeNorm_nonneg x]
      have hq_mono :
          (1 + latticeNorm p.1) ^ q ≤ (1 + latticeNorm x) ^ q := by
        exact pow_le_pow_left₀ (by linarith [latticeNorm_nonneg p.1])
          (by linarith [hp1_le]) q
      have ha :
          (latticeEnumSucc d p.1 : ℝ) ≤ C * (1 + latticeNorm x) ^ q := by
        calc
          (latticeEnumSucc d p.1 : ℝ) ≤ C * (1 + latticeNorm p.1) ^ q := hq p.1
          _ ≤ C * (1 + latticeNorm x) ^ q := by
                exact mul_le_mul_of_nonneg_left hq_mono (le_of_lt hC)
      have hb :
          (Equiv.intEquivNat p.2 : ℝ) ≤ 3 * (1 + latticeNorm x) := by
        have hb0 : (Equiv.intEquivNat p.2 : ℝ) ≤ 3 * (1 + |(p.2 : ℝ)|) :=
          intEquivNat_cast_le_three_mul p.2
        linarith
      have hpair :
          (latticeEnumSucc (d + 1) x : ℝ) ≤
            (((latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1) ^ 2) := by
        simpa [latticeEnumSucc, p, add_assoc, add_left_comm, add_comm] using
          pair_cast_le_square (latticeEnumSucc d p.1) (Equiv.intEquivNat p.2)
      have hpow_q :
          (1 + latticeNorm x) ^ q ≤ (1 + latticeNorm x) ^ (q + 1) := by
        calc
          (1 + latticeNorm x) ^ q ≤ (1 + latticeNorm x) ^ q * (1 + latticeNorm x) := by
            exact le_mul_of_one_le_right (by positivity) hA_one
          _ = (1 + latticeNorm x) ^ (q + 1) := by ring_nf
      have hpow_one :
          (1 + latticeNorm x) ≤ (1 + latticeNorm x) ^ (q + 1) := by
        calc
          (1 + latticeNorm x) ≤ (1 + latticeNorm x) * (1 + latticeNorm x) ^ q := by
            exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hA_one)
          _ = (1 + latticeNorm x) ^ (q + 1) := by ring_nf
      have ha' :
          (latticeEnumSucc d p.1 : ℝ) ≤ C * (1 + latticeNorm x) ^ (q + 1) := by
        exact le_trans ha (mul_le_mul_of_nonneg_left hpow_q (le_of_lt hC))
      have hb' :
          (Equiv.intEquivNat p.2 : ℝ) ≤ 3 * (1 + latticeNorm x) ^ (q + 1) := by
        exact le_trans hb (mul_le_mul_of_nonneg_left hpow_one (by positivity))
      have hsum :
          (latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1
            ≤ (C + 4) * (1 + latticeNorm x) ^ (q + 1) := by
        have hone : (1 : ℝ) ≤ (1 + latticeNorm x) ^ (q + 1) := one_le_pow₀ hA_one
        calc
          (latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1
              ≤ C * (1 + latticeNorm x) ^ (q + 1) +
                (3 * (1 + latticeNorm x) ^ (q + 1) + (1 + latticeNorm x) ^ (q + 1)) := by
                  linarith [ha', hb', hone]
          _ = (C + 4) * (1 + latticeNorm x) ^ (q + 1) := by ring
      have hpow2 :
          (((latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1) ^ 2)
            ≤ ((C + 4) * (1 + latticeNorm x) ^ (q + 1)) ^ 2 := by
        exact pow_le_pow_left₀ (by positivity)
          (by
            have h_nonneg :
                (0 : ℝ) ≤ (latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1 := by
                  positivity
            exact hsum) 2
      calc
        (latticeEnumSucc (d + 1) x : ℝ)
            ≤ (((latticeEnumSucc d p.1 : ℝ) + (Equiv.intEquivNat p.2 : ℝ) + 1) ^ 2) := hpair
        _ ≤ ((C + 4) * (1 + latticeNorm x) ^ (q + 1)) ^ 2 := hpow2
        _ = (C + 4) ^ 2 * (1 + latticeNorm x) ^ (2 * (q + 1)) := by
              rw [mul_pow]
              ring_nf

theorem latticeEnum_index_bound (d : ℕ) [NeZero d] :
    ∃ C > (0 : ℝ), ∃ q : ℕ, ∀ x : Fin d → ℤ,
    (latticeEnum d x : ℝ) ≤ C * (1 + latticeNorm x) ^ q := by
  cases d with
  | zero =>
      exfalso
      exact (NeZero.ne (0 : ℕ)) rfl
  | succ d =>
      simpa [latticeEnum] using latticeEnumSucc_index_bound d

/-! ### Basis and coefficients -/

/-- Delta function at a lattice site. -/
def latticeBasisAt (x : Fin d → ℤ) : RapidDecayLattice d where
  val y := if y = x then 1 else 0
  rapid_decay k := by
    apply summable_of_ne_finset_zero (s := {x})
    intro y hy
    simp only [Finset.mem_singleton] at hy
    simp [hy]

/-- The m-th basis vector: delta function at the m-th site in the enumeration. -/
def latticeBasisVec (d : ℕ) [NeZero d] (m : ℕ) : RapidDecayLattice d :=
  latticeBasisAt ((latticeEnum d).symm m)

/-- The m-th coefficient CLM: evaluation at the m-th site. -/
def latticeCoeffCLM (d : ℕ) [NeZero d] (m : ℕ) : RapidDecayLattice d →L[ℝ] ℝ where
  toLinearMap :=
    { toFun := fun a => a.val ((latticeEnum d).symm m)
      map_add' := fun _ _ => rfl
      map_smul' := fun r a => by simp [smul_eq_mul] }
  cont := by
    set f : RapidDecayLattice d →ₗ[ℝ] ℝ :=
      { toFun := fun a => a.val ((latticeEnum d).symm m)
        map_add' := fun _ _ => rfl
        map_smul' := fun r a => by simp [smul_eq_mul] }
    show Continuous f
    apply Seminorm.cont_withSeminorms_normedSpace ℝ lattice_withSeminorms
    refine ⟨{0}, 1, ?_⟩
    rw [Seminorm.le_def]
    intro a
    simp only [Seminorm.comp_apply, coe_normSeminorm, Finset.sup_singleton, one_smul]
    show ‖f a‖ ≤ latticeRapidDecaySeminorm d 0 a
    rw [Real.norm_eq_abs]
    show |a.val ((latticeEnum d).symm m)| ≤
      ∑' x, |a.val x| * (1 + latticeNorm x) ^ 0
    calc |a.val ((latticeEnum d).symm m)|
        = |a.val ((latticeEnum d).symm m)| * (1 + latticeNorm ((latticeEnum d).symm m)) ^ 0 := by
          simp [pow_zero]
      _ ≤ ∑' x, |a.val x| * (1 + latticeNorm x) ^ 0 :=
          (a.rapid_decay 0).le_tsum ((latticeEnum d).symm m)
            (fun j _ => mul_nonneg (abs_nonneg _) (weight_nonneg j 0))

/-! ### CLE to RapidDecaySeq -/

/-- Continuous linear equivalence between `RapidDecayLattice d` and `RapidDecaySeq`,
obtained by reindexing via the shell enumeration `latticeEnum d`.

The key proof obligation is that reindexing preserves rapid decay:
- Forward: use `latticeEnum_index_bound` with exponent `q` to control `(1+m)^k`
  by a lattice weight `(1+|x|)^{qk}`.
- Backward: use `latticeEnum_norm_bound` with exponent `p` to control
  `(1+|x|)^k` by a sequence weight `(1+m)^{pk}`. -/
noncomputable def latticeRapidDecayEquiv (d : ℕ) [NeZero d] :
    RapidDecayLattice d ≃L[ℝ] RapidDecaySeq := by
  let e : (Fin d → ℤ) ≃ ℕ := latticeEnum d
  let toRapidDecayLM : RapidDecayLattice d →ₗ[ℝ] RapidDecaySeq :=
    { toFun := fun a =>
        { val := fun m => a.val (e.symm m)
          rapid_decay := by
            intro k
            obtain ⟨C, hC, q, hidx⟩ := latticeEnum_index_bound d
            let k' : ℕ := q * k
            set f : (Fin d → ℤ) → ℝ := fun x =>
              |a.val x| * (1 + latticeNorm x) ^ k'
            have hf_summ : Summable f := by
              simpa [f, k'] using a.rapid_decay k'
            have hf_summ_reindexed :
                Summable (fun m : ℕ => f (e.symm m)) := e.symm.summable_iff.mpr hf_summ
            apply Summable.of_nonneg_of_le
              (fun m => by positivity)
              (fun m => ?_)
              (hf_summ_reindexed.mul_left ((C + 1) ^ k))
            have hidxm :
                (m : ℝ) ≤ C * (1 + latticeNorm (e.symm m)) ^ q := by
              simpa [e] using hidx (e.symm m)
            have ht_one :
                (1 : ℝ) ≤ (1 + latticeNorm (e.symm m)) ^ q := by
              exact one_le_pow₀ (by linarith [latticeNorm_nonneg (e.symm m)])
            have h1m :
                (1 + (m : ℝ)) ≤
                  (C + 1) * (1 + latticeNorm (e.symm m)) ^ q := by
              calc
                (1 + (m : ℝ))
                    ≤ 1 + C * (1 + latticeNorm (e.symm m)) ^ q := by linarith
                _ ≤ (1 + latticeNorm (e.symm m)) ^ q +
                      C * (1 + latticeNorm (e.symm m)) ^ q := by
                        nlinarith
                _ = (C + 1) * (1 + latticeNorm (e.symm m)) ^ q := by ring
            have hpow :
                (1 + (m : ℝ)) ^ k ≤
                  ((C + 1) * (1 + latticeNorm (e.symm m)) ^ q) ^ k := by
              exact pow_le_pow_left₀ (by positivity) h1m k
            calc
              |a.val (e.symm m)| * (1 + (m : ℝ)) ^ k
                  ≤ |a.val (e.symm m)| *
                      (((C + 1) * (1 + latticeNorm (e.symm m)) ^ q) ^ k) := by
                        exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
              _ = (C + 1) ^ k *
                    (|a.val (e.symm m)| *
                      ((1 + latticeNorm (e.symm m)) ^ q) ^ k) := by
                    rw [mul_pow]
                    ring
              _ = (C + 1) ^ k * f (e.symm m) := by
                    have hpowq :
                        ((1 + latticeNorm (e.symm m)) ^ q) ^ k =
                          (1 + latticeNorm (e.symm m)) ^ k' := by
                      simpa [k'] using (pow_mul (1 + latticeNorm (e.symm m)) q k).symm
                    simp [f, hpowq]
        }
      map_add' := by
        intro a b
        ext m
        rfl
      map_smul' := by
        intro r a
        ext m
        rfl }
  let fromRapidDecayLM : RapidDecaySeq →ₗ[ℝ] RapidDecayLattice d :=
    { toFun := fun a =>
        { val := fun x => a.val (e x)
          rapid_decay := by
            intro k
            obtain ⟨C, hC, p, hnorm⟩ := latticeEnum_norm_bound d
            let k' : ℕ := p * k
            set f : ℕ → ℝ := fun m => |a.val m| * (1 + (m : ℝ)) ^ k'
            have hf_summ : Summable f := by
              simpa [f, k'] using a.rapid_decay k'
            have hf_summ_reindexed :
                Summable (fun x : Fin d → ℤ => f (e x)) := e.summable_iff.mpr hf_summ
            apply Summable.of_nonneg_of_le
              (fun x => mul_nonneg (abs_nonneg _) (weight_nonneg x k))
              (fun x => ?_)
              (hf_summ_reindexed.mul_left ((C + 1) ^ k))
            have hnormx :
                latticeNorm x ≤ C * (1 + (e x : ℝ)) ^ p := by
              simpa [e] using hnorm (e x)
            have ht_one : (1 : ℝ) ≤ (1 + (e x : ℝ)) ^ p := by
              have hge : (0 : ℝ) ≤ (e x : ℝ) := by exact_mod_cast (Nat.zero_le (e x))
              exact one_le_pow₀ (by linarith [hge] : (1 : ℝ) ≤ 1 + (e x : ℝ))
            have h1x :
                (1 + latticeNorm x) ≤ (C + 1) * (1 + (e x : ℝ)) ^ p := by
              calc
                (1 + latticeNorm x) ≤ 1 + C * (1 + (e x : ℝ)) ^ p := by linarith
                _ ≤ (1 + (e x : ℝ)) ^ p + C * (1 + (e x : ℝ)) ^ p := by
                      nlinarith
                _ = (C + 1) * (1 + (e x : ℝ)) ^ p := by ring
            have hpow :
                (1 + latticeNorm x) ^ k ≤ ((C + 1) * (1 + (e x : ℝ)) ^ p) ^ k := by
              exact pow_le_pow_left₀ (by linarith [latticeNorm_nonneg x]) h1x k
            calc
              |a.val (e x)| * (1 + latticeNorm x) ^ k
                  ≤ |a.val (e x)| * (((C + 1) * (1 + (e x : ℝ)) ^ p) ^ k) := by
                        exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
              _ = (C + 1) ^ k * (|a.val (e x)| * ((1 + (e x : ℝ)) ^ p) ^ k) := by
                    rw [mul_pow]
                    ring
              _ = (C + 1) ^ k * f (e x) := by
                    have hpowp :
                        ((1 + (e x : ℝ)) ^ p) ^ k = (1 + (e x : ℝ)) ^ k' := by
                      simpa [k'] using (pow_mul (1 + (e x : ℝ)) p k).symm
                    simp [f, hpowp]
        }
      map_add' := by
        intro a b
        ext x
        rfl
      map_smul' := by
        intro r a
        ext x
        rfl }
  have h_to_bounded :
      Seminorm.IsBounded (latticeRapidDecaySeminorm d)
        RapidDecaySeq.rapidDecaySeminorm toRapidDecayLM := by
    intro k
    obtain ⟨C, hC, q, hidx⟩ := latticeEnum_index_bound d
    let k' : ℕ := q * k
    refine ⟨{k'}, ⟨(C + 1) ^ k, by positivity⟩, fun a => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul, toRapidDecayLM]
    show ∑' m, |a.val (e.symm m)| * (1 + (m : ℝ)) ^ k ≤
      (C + 1) ^ k * (∑' x, |a.val x| * (1 + latticeNorm x) ^ k')
    set f : (Fin d → ℤ) → ℝ := fun x => |a.val x| * (1 + (e x : ℝ)) ^ k
    have h_cov : ∑' m, |a.val (e.symm m)| * (1 + (m : ℝ)) ^ k = ∑' x, f x := by
      have h := Equiv.tsum_eq e (fun m : ℕ => |a.val (e.symm m)| * (1 + (m : ℝ)) ^ k)
      simpa [f] using h.symm
    rw [h_cov]
    have h_pw : ∀ x, f x ≤ (C + 1) ^ k * (|a.val x| * (1 + latticeNorm x) ^ k') := by
      intro x
      have hidxx : ((e x : ℕ) : ℝ) ≤ C * (1 + latticeNorm x) ^ q := by simpa [e] using hidx x
      have ht_one : (1 : ℝ) ≤ (1 + latticeNorm x) ^ q := by
        exact one_le_pow₀ (by linarith [latticeNorm_nonneg x])
      have h1x : (1 + (e x : ℝ)) ≤ (C + 1) * (1 + latticeNorm x) ^ q := by
        calc
          (1 + (e x : ℝ)) ≤ 1 + C * (1 + latticeNorm x) ^ q := by linarith
          _ ≤ (1 + latticeNorm x) ^ q + C * (1 + latticeNorm x) ^ q := by nlinarith
          _ = (C + 1) * (1 + latticeNorm x) ^ q := by ring
      have hpow :
          (1 + (e x : ℝ)) ^ k ≤ ((C + 1) * (1 + latticeNorm x) ^ q) ^ k := by
        exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + (e x : ℝ)) h1x k
      calc
        f x = |a.val x| * (1 + (e x : ℝ)) ^ k := by simp [f]
        _ ≤ |a.val x| * (((C + 1) * (1 + latticeNorm x) ^ q) ^ k) := by
              exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
        _ = (C + 1) ^ k * (|a.val x| * ((1 + latticeNorm x) ^ q) ^ k) := by
              rw [mul_pow]
              ring
        _ = (C + 1) ^ k * (|a.val x| * (1 + latticeNorm x) ^ k') := by
              have hpowq : ((1 + latticeNorm x) ^ q) ^ k = (1 + latticeNorm x) ^ k' := by
                simpa [k'] using (pow_mul (1 + latticeNorm x) q k).symm
              simp [hpowq]
    have h_summ_f : Summable f := by
      apply Summable.of_nonneg_of_le
      · intro x
        exact mul_nonneg (abs_nonneg _) (by positivity)
      · exact h_pw
      · exact (a.rapid_decay k').mul_left ((C + 1) ^ k)
    have h_le := h_summ_f.tsum_le_tsum h_pw ((a.rapid_decay k').mul_left ((C + 1) ^ k))
    simpa [tsum_mul_left] using h_le
  have h_from_bounded :
      Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
        (latticeRapidDecaySeminorm d) fromRapidDecayLM := by
    intro k
    obtain ⟨C, hC, p, hnorm⟩ := latticeEnum_norm_bound d
    let k' : ℕ := p * k
    refine ⟨{k'}, ⟨(C + 1) ^ k, by positivity⟩, fun a => ?_⟩
    simp only [Seminorm.comp_apply, Finset.sup_singleton, Seminorm.smul_apply,
      NNReal.smul_def, smul_eq_mul, fromRapidDecayLM]
    show ∑' x, |a.val (e x)| * (1 + latticeNorm x) ^ k ≤
      (C + 1) ^ k * (∑' m, |a.val m| * (1 + (m : ℝ)) ^ k')
    set g : ℕ → ℝ := fun m => |a.val m| * (1 + latticeNorm (e.symm m)) ^ k
    have h_cov : ∑' x, |a.val (e x)| * (1 + latticeNorm x) ^ k = ∑' m, g m := by
      have h := Equiv.tsum_eq e.symm (fun x : Fin d → ℤ => |a.val (e x)| * (1 + latticeNorm x) ^ k)
      simpa [g] using h.symm
    rw [h_cov]
    have h_pw : ∀ m, g m ≤ (C + 1) ^ k * (|a.val m| * (1 + (m : ℝ)) ^ k') := by
      intro m
      have hnormm : latticeNorm (e.symm m) ≤ C * (1 + (m : ℝ)) ^ p := by
        simpa [e] using hnorm m
      have ht_one : (1 : ℝ) ≤ (1 + (m : ℝ)) ^ p := by
        have hge : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
        exact one_le_pow₀ (by linarith [hge] : (1 : ℝ) ≤ 1 + (m : ℝ))
      have h1m : (1 + latticeNorm (e.symm m)) ≤ (C + 1) * (1 + (m : ℝ)) ^ p := by
        calc
          (1 + latticeNorm (e.symm m)) ≤ 1 + C * (1 + (m : ℝ)) ^ p := by linarith
          _ ≤ (1 + (m : ℝ)) ^ p + C * (1 + (m : ℝ)) ^ p := by nlinarith
          _ = (C + 1) * (1 + (m : ℝ)) ^ p := by ring
      have hpow : (1 + latticeNorm (e.symm m)) ^ k ≤ ((C + 1) * (1 + (m : ℝ)) ^ p) ^ k := by
        exact pow_le_pow_left₀ (by linarith [latticeNorm_nonneg (e.symm m)]) h1m k
      calc
        g m = |a.val m| * (1 + latticeNorm (e.symm m)) ^ k := by simp [g]
        _ ≤ |a.val m| * (((C + 1) * (1 + (m : ℝ)) ^ p) ^ k) := by
              exact mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
        _ = (C + 1) ^ k * (|a.val m| * ((1 + (m : ℝ)) ^ p) ^ k) := by
              rw [mul_pow]
              ring
        _ = (C + 1) ^ k * (|a.val m| * (1 + (m : ℝ)) ^ k') := by
              have hpowp : ((1 + (m : ℝ)) ^ p) ^ k = (1 + (m : ℝ)) ^ k' := by
                simpa [k'] using (pow_mul (1 + (m : ℝ)) p k).symm
              simp [hpowp]
    have h_summ_g : Summable g := by
      apply Summable.of_nonneg_of_le
      · intro m
        exact mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith [latticeNorm_nonneg (e.symm m)]) _)
      · exact h_pw
      · exact (a.rapid_decay k').mul_left ((C + 1) ^ k)
    have h_le := h_summ_g.tsum_le_tsum h_pw ((a.rapid_decay k').mul_left ((C + 1) ^ k))
    simpa [tsum_mul_left] using h_le
  let toRapidDecayCLM : RapidDecayLattice d →L[ℝ] RapidDecaySeq :=
    { toLinearMap := toRapidDecayLM
      cont := Seminorm.continuous_from_bounded
        (lattice_withSeminorms (d := d))
        RapidDecaySeq.rapidDecay_withSeminorms
        _ h_to_bounded }
  let fromRapidDecayCLM : RapidDecaySeq →L[ℝ] RapidDecayLattice d :=
    { toLinearMap := fromRapidDecayLM
      cont := Seminorm.continuous_from_bounded
        RapidDecaySeq.rapidDecay_withSeminorms
        (lattice_withSeminorms (d := d))
        _ h_from_bounded }
  exact ContinuousLinearEquiv.equivOfInverse
    toRapidDecayCLM
    fromRapidDecayCLM
    (by
      intro a
      ext x
      simp [toRapidDecayCLM, fromRapidDecayCLM, toRapidDecayLM, fromRapidDecayLM, e])
    (by
      intro a
      ext m
      simp [toRapidDecayCLM, fromRapidDecayCLM, toRapidDecayLM, fromRapidDecayLM, e])

/-! ### DyninMityaginSpace instance -/

/-- `RapidDecayLattice d` is a DyninMityaginSpace, established via the CLE
to `RapidDecaySeq` and the general transfer constructor `ofRapidDecayEquiv`. -/
noncomputable instance lattice_dyninMityaginSpace [NeZero d] :
    DyninMityaginSpace (RapidDecayLattice d) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    (latticeRapidDecaySeminorm d)
    lattice_withSeminorms
    (latticeRapidDecayEquiv d)

end RapidDecayLattice

/-! ### HasPointEval instance -/

/-- Rapidly decaying lattice functions can be evaluated at ℤ^d points. -/
instance rapidDecayLattice_hasPointEval (d : ℕ) :
    HasPointEval (RapidDecayLattice d) (Fin d → ℤ) where
  pointEval f x := f.val x

end GaussianField
