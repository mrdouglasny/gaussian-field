import Lattice.CirculantDFT2d

noncomputable section

namespace GaussianField

open Matrix Finset
open scoped BigOperators

variable (N : ℕ) [NeZero N]

/-- Product DFT basis function on the `d`-dimensional discrete torus. -/
def latticeFourierProductBasisFun (d : ℕ) (m : Fin d → Fin N)
    (x : FinLatticeSites d N) : ℝ :=
  ∏ i : Fin d, latticeFourierBasisFun N (m i) (x i)

/-- Squared norm of the product DFT basis vector. -/
def latticeFourierProductNormSq (d : ℕ) (m : Fin d → Fin N) : ℝ :=
  ∏ i : Fin d, latticeFourierNormSq N (m i)

/-- DFT coefficient of a function against the product basis. -/
def latticeFourierProductCoeff (d : ℕ) (f : FinLatticeSites d N → ℝ)
    (m : Fin d → Fin N) : ℝ :=
  ∑ x : FinLatticeSites d N, f x * latticeFourierProductBasisFun N d m x

@[simp] theorem latticeFourierProductNormSq_zero
    (m : Fin 0 → Fin N) :
    latticeFourierProductNormSq N 0 m = 1 := by
  simp [latticeFourierProductNormSq]

@[simp] theorem latticeFourierProductNormSq_succ (d : ℕ)
    (m₀ : Fin N) (m : Fin d → Fin N) :
    latticeFourierProductNormSq N (d + 1) (Fin.cons m₀ m) =
      latticeFourierNormSq N m₀ * latticeFourierProductNormSq N d m := by
  simp [latticeFourierProductNormSq, Fin.prod_univ_succ]

omit [NeZero N] in
private theorem sum_finModes_succ {α : Type*} [AddCommMonoid α]
    (d : ℕ) (F : (Fin (d + 1) → Fin N) → α) :
    ∑ m : (Fin (d + 1) → Fin N), F m =
      ∑ m₀ : Fin N, ∑ ms : (Fin d → Fin N), F (Fin.cons m₀ ms) := by
  let e : (Fin (d + 1) → Fin N) ≃ Fin N × (Fin d → Fin N) :=
    { toFun := fun x => (x 0, fun i => x i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := by
        intro x
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      right_inv := by
        intro p
        cases p
        rfl }
  calc
    ∑ m : (Fin (d + 1) → Fin N), F m
      = ∑ p : Fin N × (Fin d → Fin N), F (Fin.cons p.1 p.2) := by
          exact Fintype.sum_equiv e
            (fun m : (Fin (d + 1) → Fin N) => F m)
            (fun p : Fin N × (Fin d → Fin N) => F (Fin.cons p.1 p.2))
            (fun m => by
              simpa [e] using congrArg F (e.left_inv m).symm)
    _ = ∑ m₀ : Fin N, ∑ ms : (Fin d → Fin N), F (Fin.cons m₀ ms) := by
          rw [Fintype.sum_prod_type]

/-- Split a sum over `(ZMod N)^(d+1)` into the first coordinate and the tail. -/
theorem sum_finLatticeSites_succ {α : Type*} [AddCommMonoid α]
    (d : ℕ) (F : FinLatticeSites (d + 1) N → α) :
    ∑ x : FinLatticeSites (d + 1) N, F x =
      ∑ z : ZMod N, ∑ xs : FinLatticeSites d N, F (Fin.cons z xs) := by
  let e : FinLatticeSites (d + 1) N ≃ ZMod N × FinLatticeSites d N :=
    { toFun := fun x => (x 0, fun i => x i.succ)
      invFun := fun p => Fin.cons p.1 p.2
      left_inv := by
        intro x
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      right_inv := by
        intro p
        cases p
        rfl }
  calc
    ∑ x : FinLatticeSites (d + 1) N, F x
      = ∑ p : ZMod N × FinLatticeSites d N, F (Fin.cons p.1 p.2) := by
          exact Fintype.sum_equiv e
            (fun x : FinLatticeSites (d + 1) N => F x)
            (fun p : ZMod N × FinLatticeSites d N => F (Fin.cons p.1 p.2))
            (fun x => by
              simpa [e] using congrArg F (e.left_inv x).symm)
    _ = ∑ z : ZMod N, ∑ xs : FinLatticeSites d N, F (Fin.cons z xs) := by
          rw [Fintype.sum_prod_type]

/-- Recursive decomposition of product DFT coefficients. -/
theorem latticeFourierProductCoeff_succ (d : ℕ)
    (f : FinLatticeSites (d + 1) N → ℝ) (m₀ : Fin N) (m : Fin d → Fin N) :
    latticeFourierProductCoeff N (d + 1) f (Fin.cons m₀ m) =
      ∑ z : ZMod N,
        latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
          latticeFourierBasisFun N m₀ z := by
  unfold latticeFourierProductCoeff
  rw [sum_finLatticeSites_succ (N := N) d
    (F := fun x : FinLatticeSites (d + 1) N =>
      f x * latticeFourierProductBasisFun N (d + 1) (Fin.cons m₀ m) x)]
  refine Finset.sum_congr rfl ?_
  intro z hz
  simp_rw [latticeFourierProductBasisFun, Fin.prod_univ_succ]
  calc
    ∑ xs : FinLatticeSites d N,
        f (Fin.cons z xs) *
          (latticeFourierBasisFun N m₀ z *
            latticeFourierProductBasisFun N d m xs)
      = ∑ xs : FinLatticeSites d N,
          (f (Fin.cons z xs) * latticeFourierProductBasisFun N d m xs) *
            latticeFourierBasisFun N m₀ z := by
              refine Finset.sum_congr rfl ?_
              intro xs hxs
              ring
    _ = latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
          latticeFourierBasisFun N m₀ z := by
            rw [latticeFourierProductCoeff, Finset.sum_mul]

/-- The squared norm of a product basis vector factors coordinatewise. -/
theorem latticeFourierProductBasis_sq_sum
    : ∀ d : ℕ, ∀ m : Fin d → Fin N,
      ∑ x : FinLatticeSites d N, latticeFourierProductBasisFun N d m x ^ 2 =
        latticeFourierProductNormSq N d m
  | 0, m => by
      simp [latticeFourierProductBasisFun, latticeFourierProductNormSq, latticeFourierNormSq]
  | d + 1, m => by
      rw [sum_finLatticeSites_succ (N := N) d
        (F := fun x : FinLatticeSites (d + 1) N =>
          latticeFourierProductBasisFun N (d + 1) m x ^ 2)]
      simp_rw [latticeFourierProductBasisFun, Fin.prod_univ_succ]
      rw [Finset.sum_comm]
      calc
        ∑ xs : FinLatticeSites d N,
            ∑ z : ZMod N,
              (latticeFourierBasisFun N (m 0) z *
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs) ^ 2
          = ∑ xs : FinLatticeSites d N,
              ∑ z : ZMod N,
                latticeFourierBasisFun N (m 0) z ^ 2 *
                  latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                    refine Finset.sum_congr rfl ?_
                    intro xs hx
                    refine Finset.sum_congr rfl ?_
                    intro z hz
                    ring
        _ = ∑ xs : FinLatticeSites d N,
              (∑ z : ZMod N, latticeFourierBasisFun N (m 0) z ^ 2) *
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                  refine Finset.sum_congr rfl ?_
                  intro xs hx
                  rw [Finset.sum_mul]
        _ = (∑ z : ZMod N, latticeFourierBasisFun N (m 0) z ^ 2) *
              ∑ xs : FinLatticeSites d N,
                latticeFourierProductBasisFun N d (fun i => m i.succ) xs ^ 2 := by
                  rw [← Finset.mul_sum]
        _ = latticeFourierNormSq N (m 0) *
              latticeFourierProductNormSq N d (fun i => m i.succ) := by
                  rw [latticeFourierNormSq, latticeFourierProductBasis_sq_sum d
                    (fun i => m i.succ)]
        _ = latticeFourierProductNormSq N (d + 1) m := by
                  have hm : m = Fin.cons (m 0) (fun i => m i.succ) := by
                    funext i
                    refine Fin.cases ?_ ?_ i
                    · rfl
                    · intro j
                      rfl
                  rw [hm, latticeFourierProductNormSq_succ]
                  simp

/-- Product DFT norms are strictly positive. -/
theorem latticeFourierProductNormSq_pos :
    ∀ d : ℕ, ∀ m : Fin d → Fin N, 0 < latticeFourierProductNormSq N d m
  | 0, m => by
      simp [latticeFourierProductNormSq]
  | d + 1, m => by
      have hm : m = Fin.cons (m 0) (fun i => m i.succ) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hm]
      rw [latticeFourierProductNormSq_succ]
      exact mul_pos (latticeFourierNormSq_pos N (m 0) (m 0).isLt)
        (latticeFourierProductNormSq_pos d (fun i => m i.succ))

/-- Parseval identity for the `d`-dimensional product DFT basis. -/
theorem dft_parseval_family :
    ∀ d : ℕ, ∀ f g : FinLatticeSites d N → ℝ,
      ∑ x : FinLatticeSites d N, f x * g x =
        ∑ m : (Fin d → Fin N),
          latticeFourierProductCoeff N d f m *
            latticeFourierProductCoeff N d g m /
            latticeFourierProductNormSq N d m
  | 0, f, g => by
      simp [latticeFourierProductCoeff, latticeFourierProductNormSq,
        latticeFourierProductBasisFun]
  | d + 1, f, g => by
      rw [sum_finLatticeSites_succ (N := N) d
        (F := fun x : FinLatticeSites (d + 1) N => f x * g x)]
      have hinner :
          ∀ z : ZMod N,
            ∑ xs : FinLatticeSites d N, f (Fin.cons z xs) * g (Fin.cons z xs) =
              ∑ m : (Fin d → Fin N),
                latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                  latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m /
                  latticeFourierProductNormSq N d m := by
        intro z
        simpa using
          dft_parseval_family d
            (fun xs => f (Fin.cons z xs))
            (fun xs => g (Fin.cons z xs))
      simp_rw [hinner]
      rw [Finset.sum_comm]
      have h1d :
          ∀ m : (Fin d → Fin N),
            ∑ z : ZMod N,
              latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m =
              ∑ m₀ : Fin N,
                (∑ z : ZMod N,
                    latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                      latticeFourierBasisFun N m₀ z) *
                  (∑ z : ZMod N,
                    latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m *
                      latticeFourierBasisFun N m₀ z) /
                  latticeFourierNormSq N m₀ := by
        intro m
        simpa using
          (dft_parseval_1d N
            (fun z => latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m)
            (fun z => latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m))
      calc
        ∑ m : (Fin d → Fin N),
            ∑ z : ZMod N,
              latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m /
                latticeFourierProductNormSq N d m
          = ∑ m : (Fin d → Fin N),
              (latticeFourierProductNormSq N d m)⁻¹ *
                ∑ z : ZMod N,
                  latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                    latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      calc
                        ∑ z : ZMod N,
                            latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                              latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m /
                              latticeFourierProductNormSq N d m
                          = ∑ z : ZMod N,
                              (latticeFourierProductNormSq N d m)⁻¹ *
                                (latticeFourierProductCoeff N d
                                  (fun xs => f (Fin.cons z xs)) m *
                                  latticeFourierProductCoeff N d
                                    (fun xs => g (Fin.cons z xs)) m) := by
                                    refine Finset.sum_congr rfl ?_
                                    intro z hz
                                    rw [div_eq_mul_inv, mul_comm]
                        _ = (latticeFourierProductNormSq N d m)⁻¹ *
                              ∑ z : ZMod N,
                                latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                                  latticeFourierProductCoeff N d
                                    (fun xs => g (Fin.cons z xs)) m := by
                                    rw [← Finset.mul_sum]
        _ = ∑ m : (Fin d → Fin N),
              (latticeFourierProductNormSq N d m)⁻¹ *
                ∑ m₀ : Fin N,
                  (∑ z : ZMod N,
                      latticeFourierProductCoeff N d (fun xs => f (Fin.cons z xs)) m *
                        latticeFourierBasisFun N m₀ z) *
                    (∑ z : ZMod N,
                      latticeFourierProductCoeff N d (fun xs => g (Fin.cons z xs)) m *
                        latticeFourierBasisFun N m₀ z) /
                    latticeFourierNormSq N m₀ := by
                      refine Finset.sum_congr rfl ?_
                      intro m hm
                      rw [h1d m]
        _ = ∑ m : (Fin d → Fin N),
              ∑ m₀ : Fin N,
                latticeFourierProductCoeff N (d + 1) f (Fin.cons m₀ m) *
                  latticeFourierProductCoeff N (d + 1) g (Fin.cons m₀ m) /
                  (latticeFourierNormSq N m₀ * latticeFourierProductNormSq N d m) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro m₀ hm₀
                    rw [← latticeFourierProductCoeff_succ (N := N) d f m₀ m,
                      ← latticeFourierProductCoeff_succ (N := N) d g m₀ m]
                    have hnorm₀ : latticeFourierNormSq N m₀ ≠ 0 :=
                      ne_of_gt (latticeFourierNormSq_pos N m₀ m₀.isLt)
                    have hnormd : latticeFourierProductNormSq N d m ≠ 0 :=
                      ne_of_gt (latticeFourierProductNormSq_pos (N := N) d m)
                    field_simp [hnorm₀, hnormd]
        _ = ∑ m₀ : Fin N, ∑ m : (Fin d → Fin N),
              latticeFourierProductCoeff N (d + 1) f (Fin.cons m₀ m) *
                latticeFourierProductCoeff N (d + 1) g (Fin.cons m₀ m) /
                (latticeFourierNormSq N m₀ * latticeFourierProductNormSq N d m) := by
                    rw [Finset.sum_comm]
        _ = ∑ m₀ : Fin N, ∑ m : (Fin d → Fin N),
              latticeFourierProductCoeff N (d + 1) f (Fin.cons m₀ m) *
                latticeFourierProductCoeff N (d + 1) g (Fin.cons m₀ m) /
                latticeFourierProductNormSq N (d + 1) (Fin.cons m₀ m) := by
                    refine Finset.sum_congr rfl ?_
                    intro m₀ hm₀
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    rw [latticeFourierProductNormSq_succ]
        _ = ∑ m : (Fin (d + 1) → Fin N),
              latticeFourierProductCoeff N (d + 1) f m *
                latticeFourierProductCoeff N (d + 1) g m /
                latticeFourierProductNormSq N (d + 1) m := by
                    symm
                    exact sum_finModes_succ (N := N) d
                      (F := fun m : (Fin (d + 1) → Fin N) =>
                        latticeFourierProductCoeff N (d + 1) f m *
                          latticeFourierProductCoeff N (d + 1) g m /
                          latticeFourierProductNormSq N (d + 1) m)

/-- The mass operator is surjective in every finite dimension. -/
theorem massOperator_surjective (d : ℕ) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    Function.Surjective (massOperator d N a mass) := by
  have hinj : Function.Injective (massOperator d N a mass) := by
    intro f g hfg
    by_contra hne
    have hne' : f - g ≠ 0 := sub_ne_zero.mpr hne
    have hpos := massOperator_pos_def d N a mass ha hmass (f - g) hne'
    have hzero : ∑ x, (f - g) x * (massOperator d N a mass (f - g)) x = 0 := by
      have : massOperator d N a mass (f - g) = 0 := by
        ext x
        simp [map_sub, hfg, sub_self]
      simp [this]
    linarith
  exact (massOperator d N a mass).toLinearMap.surjective_of_injective hinj

omit [NeZero N] in
private lemma latticeFourierProductBasisFun_update (d : ℕ) (m : Fin d → Fin N)
    (x : FinLatticeSites d N) (i : Fin d) (z : ZMod N) :
    latticeFourierProductBasisFun N d m (Function.update x i z) =
      latticeFourierBasisFun N (m i) z *
        Finset.prod (Finset.univ \ {i}) (fun j => latticeFourierBasisFun N (m j) (x j)) := by
  unfold latticeFourierProductBasisFun
  calc
    ∏ j : Fin d, latticeFourierBasisFun N (m j) ((Function.update x i z) j)
      = latticeFourierBasisFun N (m i) z *
          Finset.prod (Finset.univ \ {i})
            (fun j => latticeFourierBasisFun N (m j) ((Function.update x i z) j)) := by
              simpa [Function.update] using
                (Finset.prod_eq_mul_prod_diff_singleton (s := Finset.univ) i
                  (fun j => latticeFourierBasisFun N (m j) ((Function.update x i z) j))
                  (by
                    intro hi
                    exact False.elim (hi (Finset.mem_univ i))))
    _ = latticeFourierBasisFun N (m i) z *
          Finset.prod (Finset.univ \ {i}) (fun j => latticeFourierBasisFun N (m j) (x j)) := by
            congr 1
            refine Finset.prod_congr rfl ?_
            intro j hj
            have hji : j ≠ i := by
              simpa [Finset.mem_singleton] using
                (show j ∈ Finset.univ ∧ j ∉ ({i} : Finset (Fin d)) from by
                  simpa [Finset.mem_sdiff] using hj)
            simp [Function.update, hji]

/-- A product of 1D DFT modes is an eigenvector of the `d`-dimensional mass
operator with eigenvalue `Σᵢ λᵢ + mass²`. -/
theorem massOperator_product_eigenvector_family (d : ℕ) (a mass : ℝ) (ha : a ≠ 0)
    (m : Fin d → Fin N) (x : FinLatticeSites d N) :
    (massOperator d N a mass (latticeFourierProductBasisFun N d m)) x =
      ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
        latticeFourierProductBasisFun N d m x := by
  have hplus : ∀ i : Fin d,
      (fun j => if j = i then x j + 1 else x j) = Function.update x i (x i + 1) := by
    intro i
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  have hminus : ∀ i : Fin d,
      (fun j => if j = i then x j - 1 else x j) = Function.update x i (x i - 1) := by
    intro i
    funext j
    by_cases hji : j = i <;> simp [Function.update, hji]
  have hcoord : ∀ i : Fin d,
      -(a⁻¹ ^ 2 *
          (((latticeFourierProductBasisFun N d m fun j => if j = i then x j + 1 else x j) +
              latticeFourierProductBasisFun N d m (fun j => if j = i then x j - 1 else x j)) -
            2 * latticeFourierProductBasisFun N d m x)) =
        latticeEigenvalue1d N a (m i) * latticeFourierProductBasisFun N d m x := by
    intro i
    have h1d := dft_1d_eigenvalue_pointwise N a ha (m i) (m i).isLt (x i)
    set tail : ℝ := Finset.prod (Finset.univ \ {i})
      (fun j => latticeFourierBasisFun N (m j) (x j))
    have hself :
        latticeFourierProductBasisFun N d m x =
          latticeFourierBasisFun N (m i) (x i) * tail := by
      simpa [tail, Function.update_self] using
        (latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i))
    rw [hplus i]
    rw [latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i + 1)]
    rw [hminus i]
    rw [latticeFourierProductBasisFun_update (N := N) (d := d) (m := m) (x := x) (i := i)
          (z := x i - 1)]
    rw [hself]
    linear_combination
      tail * h1d
  have hcoord_update : ∀ i : Fin d,
      -(a⁻¹ ^ 2 *
          ((latticeFourierProductBasisFun N d m (Function.update x i (x i + 1)) +
              latticeFourierProductBasisFun N d m (Function.update x i (x i - 1))) -
            2 * latticeFourierProductBasisFun N d m x)) =
        latticeEigenvalue1d N a (m i) * latticeFourierProductBasisFun N d m x := by
    intro i
    simpa [hplus i, hminus i] using hcoord i
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun]
  calc
    -(a⁻¹ ^ 2 *
        ∑ i : Fin d,
          (((latticeFourierProductBasisFun N d m fun j => if j = i then x j + 1 else x j) +
              latticeFourierProductBasisFun N d m (fun j => if j = i then x j - 1 else x j)) -
            2 * latticeFourierProductBasisFun N d m x)) +
        mass ^ 2 * latticeFourierProductBasisFun N d m x
      = -(a⁻¹ ^ 2 *
          ∑ i : Fin d,
            ((latticeFourierProductBasisFun N d m (Function.update x i (x i + 1)) +
                latticeFourierProductBasisFun N d m (Function.update x i (x i - 1))) -
              2 * latticeFourierProductBasisFun N d m x)) +
          mass ^ 2 * latticeFourierProductBasisFun N d m x := by
            refine congrArg
              (fun t : ℝ => -(a⁻¹ ^ 2 * t) + mass ^ 2 * latticeFourierProductBasisFun N d m x) ?_
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [hplus i, hminus i]
    _
      = (∑ i : Fin d, latticeEigenvalue1d N a (m i) *
            latticeFourierProductBasisFun N d m x) +
          mass ^ 2 * latticeFourierProductBasisFun N d m x := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            simpa using (Finset.sum_congr rfl (fun i _ => hcoord_update i))
    _ = ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
          latticeFourierProductBasisFun N d m x := by
            rw [← Finset.sum_mul]
            ring

/-- Applying the mass operator to a field multiplies each product DFT
eigen-coefficient by the corresponding explicit eigenvalue. -/
theorem dft_eigencoeff_massOperator_family (d : ℕ) (a mass : ℝ) (ha : a ≠ 0)
    (m : Fin d → Fin N) (h : FinLatticeSites d N → ℝ) :
    latticeFourierProductCoeff N d (massOperator d N a mass h) m =
      ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
        latticeFourierProductCoeff N d h m := by
  unfold latticeFourierProductCoeff
  calc
    ∑ x : FinLatticeSites d N,
        (massOperator d N a mass h) x * latticeFourierProductBasisFun N d m x
      = ∑ x : FinLatticeSites d N,
          latticeFourierProductBasisFun N d m x * (massOperator d N a mass h) x := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            rw [mul_comm]
    _ = ∑ x : FinLatticeSites d N,
          (massOperator d N a mass (latticeFourierProductBasisFun N d m)) x * h x := by
            rw [massOperator_selfAdjoint d N a mass (latticeFourierProductBasisFun N d m) h]
    _ = ∑ x : FinLatticeSites d N,
          (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
            latticeFourierProductBasisFun N d m x) * h x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              rw [massOperator_product_eigenvector_family (N := N) d a mass ha m x]
    _ = ((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
          ∑ x : FinLatticeSites d N, h x * latticeFourierProductBasisFun N d m x := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring

/-- The abstract spectral covariance equals the explicit product-DFT spectral
sum in arbitrary dimension. -/
theorem abstract_spectral_eq_dft_spectral_family (d : ℕ) (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeSites d N → ℝ) :
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g =
      ∑ m : (Fin d → Fin N),
        latticeFourierProductCoeff N d f m *
          latticeFourierProductCoeff N d g m /
          (((∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2) *
            latticeFourierProductNormSq N d m) := by
  obtain ⟨h, rfl⟩ := massOperator_surjective (N := N) d a mass ha hmass g
  have ha' : a ≠ 0 := ne_of_gt ha
  trans ∑ x : FinLatticeSites d N, f x * h x
  · rw [lattice_covariance_eq_spectral]
    simp_rw [massOperator_eigenCoeff_eq_eigenvalues_mul_eigenCoeff (d := d) (N := N) a mass h]
    refine Eq.trans ?_
      (massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass f h)
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hne : massEigenvalues d N a mass k ≠ 0 :=
      ne_of_gt (massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k)
    field_simp [hne]
  · rw [dft_parseval_family (N := N) d f h]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [dft_eigencoeff_massOperator_family (N := N) d a mass ha' m h]
    have hμ_pos :
        0 < (∑ i : Fin d, latticeEigenvalue1d N a (m i)) + mass ^ 2 := by
      have hsum_nonneg : 0 ≤ ∑ i : Fin d, latticeEigenvalue1d N a (m i) :=
        Finset.sum_nonneg (fun i _ => latticeEigenvalue1d_nonneg N a (m i))
      positivity
    have hnorm_pos : 0 < latticeFourierProductNormSq N d m :=
      latticeFourierProductNormSq_pos (N := N) d m
    field_simp [ne_of_gt hμ_pos, ne_of_gt hnorm_pos]

end GaussianField

end
