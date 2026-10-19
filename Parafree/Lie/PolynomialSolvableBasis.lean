import Parafree.Lie.PolynomialSolvableUniversal

/-! Extending an orbit on the monomial basis to the polynomial solvable algebra. -/
noncomputable section
namespace Parafree.Lie.PolynomialSolvable
open Polynomial Algebra
variable {R : Type*} [CommRing R] {k : R}
variable {L : Type*} [LieRing L] [LieAlgebra R L]

def polynomialFamily (f : ℕ → L) : Polynomial R →ₗ[R] L :=
  (basisMonomials R).constr R f

@[simp] theorem polynomialFamily_X_pow (f : ℕ → L) (n : ℕ) :
    polynomialFamily f (X^n : Polynomial R) = f n := by
  simpa only [polynomialFamily, coe_basisMonomials, ← C_mul_X_pow_eq_monomial,
    map_one, one_mul] using (basisMonomials R).constr_basis R f n

/-- Linear induction using scalar multiples of powers of `X`. -/
theorem polynomial_induction {P : Polynomial R → Prop}
    (hadd : ∀ p q, P p → P q → P (p+q))
    (hsmul : ∀ (r:R) p, P p → P (r • p))
    (hpow : ∀ n, P (X^n)) (p : Polynomial R) : P p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact hadd p q hp hq
  | monomial n r =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul]
    exact hsmul r _ (hpow n)

theorem euler_X_pow (n : ℕ) :
    X * derivative (X^n : Polynomial R) - X^n = ((n:R)-1) • X^n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_X_pow_succ]
    simp only [smul_eq_C_mul, map_sub, map_one, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

def liftDataOfBasis (t s e : L) (f : ℕ → L)
    (hff : ∀ i j, ⁅f i,f j⁆ = 0)
    (hs : ∀ n, ⁅s,f n⁆ = f (n+1))
    (he : ∀ n, ⁅e,f n⁆ = k • f (n+2))
    (ht : ∀ n, ⁅t,f n⁆ = ((n:R)-1) • f n)
    (hse : ⁅s,e⁆ = 0) (hts : ⁅t,s⁆ = s) (hte : ⁅t,e⁆ = (2:R) • e) :
    LiftData (R := R) (k := k) (L := L) where
  t := t
  s := s
  e := e
  family := polynomialFamily f
  family_commute p q := by
    induction p using polynomial_induction with
    | hadd p p' hp hp' => simp only [map_add, add_lie, hp, hp', add_zero]
    | hsmul r p hp => simp only [map_smul, smul_lie, hp, smul_zero]
    | hpow i =>
      induction q using polynomial_induction with
      | hadd q q' hq hq' => simp only [map_add, lie_add, hq, hq', add_zero]
      | hsmul r q hq => simp only [map_smul, lie_smul, hq, smul_zero]
      | hpow j => simp only [polynomialFamily_X_pow, hff]
  s_family p := by
    induction p using polynomial_induction with
    | hadd p q hp hq => simp only [map_add, lie_add, mul_add, hp, hq]
    | hsmul r p hp => simp only [map_smul, lie_smul, mul_smul_comm, hp]
    | hpow n => rw [polynomialFamily_X_pow, hs, ← pow_succ', polynomialFamily_X_pow]
  e_family p := by
    induction p using polynomial_induction with
    | hadd p q hp hq => simp only [map_add, lie_add, mul_add, hp, hq, smul_add]
    | hsmul r p hp => simp only [map_smul, lie_smul, mul_smul_comm, hp, smul_comm r k]
    | hpow n =>
      rw [polynomialFamily_X_pow, he,
        show (X:Polynomial R)^2*X^n = X^(n+2) by rw [← pow_add, Nat.add_comm],
        polynomialFamily_X_pow]
  t_family p := by
    induction p using polynomial_induction with
    | hadd p q hp hq =>
      simp only [map_add, lie_add, mul_add, add_sub_add_comm, hp, hq]
    | hsmul r p hp =>
      simp only [map_smul, lie_smul, mul_smul_comm, ← smul_sub, hp]
    | hpow n => rw [polynomialFamily_X_pow, ht, euler_X_pow, map_smul, polynomialFamily_X_pow]
  s_e := hse
  t_s := hts
  t_e := hte

/-- Homomorphisms are determined by the weight element, the two shifts, and
all polynomial monomials. -/
theorem hom_ext {f g : Algebra R k →ₗ⁅R⁆ L}
    (ht : f (T R k) = g (T R k)) (hs : f (S R k) = g (S R k))
    (he : f (E R k) = g (E R k)) (hm : ∀ n, f (M R k n) = g (M R k n)) : f = g := by
  have hp (p : Polynomial R) : f (polynomial R k p) = g (polynomial R k p) := by
    induction p using polynomial_induction with
    | hadd p q hp hq => simp only [map_add, hp, hq]
    | hsmul r p hp => simp only [map_smul, hp]
    | hpow n => exact hm n
  ext z
  rw [decomposition z]
  simp only [map_add, map_smul, hp, ht, hs, he]

end Parafree.Lie.PolynomialSolvable
