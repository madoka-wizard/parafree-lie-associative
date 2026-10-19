import Parafree.Linear.DividedFiltration

/-! Finite divided sums and their common denominator.
The witness for divisibility may use a larger finite stage: both families are
zero-extended to a common bound before applying the cancellation theorem. -/

namespace Parafree.Linear.DividedFiltration

variable {R S M V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]

/-- The finite sum of the divided representatives. -/
def dividedSum (ι : M →ₗ[R] V) (b : S) (x : ℕ → M) : ℕ → V
  | 0 => ι (x 0)
  | n + 1 => dividedSum ι b x n + b ^ (n + 1) • ι (x (n + 1))

/-- Clearing a common denominator is an exact equality. -/
theorem numerator_image (ι : M →ₗ[R] V) (p : R) (b : S)
    (hb : algebraMap R S p * b = 1) (x : ℕ → M) (n : ℕ) :
    ι (numerator p x n) = (algebraMap R S p) ^ n • dividedSum ι b x n := by
  induction n with
  | zero => simp [dividedSum]
  | succ n ih =>
    have hcancel : (algebraMap R S p) ^ (n + 1) * b ^ (n + 1) = 1 := by
      rw [← mul_pow, hb, one_pow]
    rw [numerator_succ, map_add, map_smul, ih, dividedSum, smul_add, smul_smul,
      hcancel, one_smul]
    congr 1
    rw [← IsScalarTower.algebraMap_smul S p, smul_smul, pow_succ']

/-- Actual equality of divided sums implies equality after clearing denominators. -/
theorem numerator_eq_smul_of_dividedSum (ι : M →ₗ[R] V)
    (hι : Function.Injective ι) (p : R) (b : S)
    (hb : algebraMap R S p * b = 1) (x y : ℕ → M) (n : ℕ)
    (h : dividedSum ι b x n = p • dividedSum ι b y n) :
    numerator p x n = p • numerator p y n := by
  apply hι
  rw [map_smul, numerator_image ι p b hb, numerator_image ι p b hb, h]
  exact smul_comm _ _ _

/-- The finite injectivity theorem in the ambient scalar extension. -/
theorem term_decomposition_of_dividedSum
    (E : ℕ → Submodule R M) (hE : Antitone E) (p : R) (hs : Saturated E p)
    (ι : M →ₗ[R] V) (hι : Function.Injective ι) (b : S)
    (hb : algebraMap R S p * b = 1) (x y : ℕ → M) (n : ℕ)
    (hx : ∀ j ≤ n, x j ∈ E j) (hy : ∀ j ≤ n, y j ∈ E j)
    (h : dividedSum ι b x n = p • dividedSum ι b y n) (j : ℕ) (hj : j ≤ n) :
    ∃ a ∈ E (j + 1), ∃ c ∈ E j, x j = a + p • c :=
  term_decomposition_of_divisible E p hE hs x y n hx hy
    (numerator_eq_smul_of_dividedSum ι hι p b hb x y n h) j hj

open scoped BigOperators

/-- Evaluation of an arbitrary finitely supported family of divided terms. -/
def finiteSum (ι : M →ₗ[R] V) (b : S) (x : ℕ →₀ M) : V :=
  x.sum (fun j m => b ^ j • ι m)

omit [Algebra R S] [IsScalarTower R S V] in
theorem dividedSum_eq_sum (ι : M →ₗ[R] V) (b : S) (x : ℕ → M) (n : ℕ) :
    dividedSum ι b x n = ∑ j ∈ Finset.range (n + 1), b ^ j • ι (x j) := by
  induction n with
  | zero => simp [dividedSum]
  | succ n ih => rw [dividedSum, ih, Finset.sum_range_succ (n := n + 1)]

omit [Algebra R S] [IsScalarTower R S V] in
theorem finiteSum_eq_dividedSum (ι : M →ₗ[R] V) (b : S) (x : ℕ →₀ M) (n : ℕ)
    (hn : ∀ j ∈ x.support, j ≤ n) : finiteSum ι b x = dividedSum ι b x n := by
  rw [dividedSum_eq_sum]
  exact x.sum_of_support_subset (fun j hj => Finset.mem_range.mpr (by
    have := hn j hj
    omega)) _ (fun _ _ => by simp only [map_zero, smul_zero])

/-- Cancellation with an arbitrary finite divisibility witness. The proof chooses
one bound for both supports and the coefficient being tested. -/
theorem term_decomposition_of_finiteSum
    (E : ℕ → Submodule R M) (hE : Antitone E) (p : R) (hs : Saturated E p)
    (ι : M →ₗ[R] V) (hι : Function.Injective ι) (b : S)
    (hb : algebraMap R S p * b = 1) (x y : ℕ →₀ M)
    (hx : ∀ j, x j ∈ E j) (hy : ∀ j, y j ∈ E j)
    (h : finiteSum ι b x = p • finiteSum ι b y) (j : ℕ) :
    ∃ a ∈ E (j + 1), ∃ c ∈ E j, x j = a + p • c := by
  let n := max j (max (x.support.sup id) (y.support.sup id))
  have hxn : ∀ k ∈ x.support, k ≤ n := by
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  have hyn : ∀ k ∈ y.support, k ≤ n := by
    intro k hk
    exact (Finset.le_sup (f := id) hk).trans
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  rw [finiteSum_eq_dividedSum ι b x n hxn, finiteSum_eq_dividedSum ι b y n hyn] at h
  exact term_decomposition_of_dividedSum E hE p hs ι hι b hb x y n
    (fun k _ => hx k) (fun k _ => hy k) h j (Nat.le_max_left _ _)

end Parafree.Linear.DividedFiltration
