import Parafree.Lie.PolynomialSolvableBasis
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc

/-! A cubic alternating polynomial form constructed by separating exponents
modulo three. Its shift invariance avoids a general alternant decomposition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.Linear.PolynomialCubic
open Polynomial
open Parafree.Lie.PolynomialSolvable (polynomial_induction euler_X_pow)
variable (R : Type*) [CommRing R]
abbrev V := Fin 3 → Polynomial R

def monomialVector (n : ℕ) : V R := fun i => if n % 3 = i.val then X^n else 0

def split : Polynomial R →ₗ[R] V R := (basisMonomials R).constr R (monomialVector R)

@[simp] theorem split_X_pow (n : ℕ) : split R (X^n) = monomialVector R n := by
  simpa only [split, coe_basisMonomials, ← C_mul_X_pow_eq_monomial, map_one, one_mul]
    using (basisMonomials R).constr_basis R (monomialVector R) n

@[simp] theorem split_C_mul (c : R) (p : Polynomial R) (i : Fin 3) :
    split R (C c * p) i = C c * split R p i := by
  simp only [← smul_eq_C_mul, map_smul, Pi.smul_apply]

def rotate (v : V R) : V R := ![v 2,v 0,v 1]

theorem split_X (p : Polynomial R) (i : Fin 3) :
    split R (X*p) i = X * rotate R (split R p) i := by
  induction p using polynomial_induction with
  | hadd p q hp hq => simp only [mul_add, map_add, Pi.add_apply, hp, hq, rotate]; fin_cases i <;> simp [mul_add]
  | hsmul r p hp =>
    simp only [mul_smul_comm, map_smul, Pi.smul_apply, hp, rotate]
    fin_cases i <;> simp
  | hpow n =>
    rw [← pow_succ', split_X_pow, split_X_pow]
    have hb : n % 3 < 3 := Nat.mod_lt _ (by decide)
    generalize hn : n % 3 = r at hb ⊢
    interval_cases r <;> fin_cases i <;>
      simp [monomialVector, rotate, Nat.add_mod, hn, pow_succ']

theorem split_euler (p : Polynomial R) (i : Fin 3) :
    split R (X*derivative p-p) i = X*derivative (split R p i)-split R p i := by
  induction p using polynomial_induction with
  | hadd p q hp hq =>
    simp only [map_add, mul_add, add_sub_add_comm, Pi.add_apply, hp, hq]
  | hsmul r p hp =>
    simp only [map_smul, mul_smul_comm, ← smul_sub, Pi.smul_apply, hp]
  | hpow n =>
    rw [euler_X_pow, map_smul, split_X_pow]
    simp only [Pi.smul_apply, monomialVector]
    split_ifs <;> simp [euler_X_pow]

theorem split_X_derivative (p : Polynomial R) (i : Fin 3) :
    split R (X * derivative p) i = X * derivative (split R p i) := by
  have h := split_euler R p i
  simp only [map_sub, Pi.sub_apply] at h
  have h' := congrArg (fun q : Polynomial R => q + split R p i) h
  simpa only [sub_add_cancel] using h'

def determinant : AlternatingMap R (V R) (Polynomial R) (Fin 3) :=
  { toMultilinearMap :=
      (Matrix.detRowAlternating : AlternatingMap (Polynomial R) (V R) (Polynomial R) (Fin 3)).toMultilinearMap.restrictScalars R
    map_eq_zero_of_eq' := by
      intro v i j h hij
      exact (Matrix.detRowAlternating (R := Polynomial R)).map_eq_zero_of_eq v h hij }

def form : AlternatingMap R (Polynomial R) (Polynomial R) (Fin 3) :=
  (determinant R).compLinearMap (split R)

def value (p q r : Polynomial R) : Polynomial R := form R ![p,q,r]

theorem value_formula (p q r : Polynomial R) :
    value R p q r =
      split R p 0 * split R q 1 * split R r 2 +
      split R p 1 * split R q 2 * split R r 0 +
      split R p 2 * split R q 0 * split R r 1 -
      split R p 2 * split R q 1 * split R r 0 -
      split R p 1 * split R q 0 * split R r 2 -
      split R p 0 * split R q 2 * split R r 1 := by
  change Matrix.det (fun i => split R (![p,q,r] i)) = _
  rw [Matrix.det_fin_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem shift_invariant (p q r : Polynomial R) :
    value R (X*p) q r + value R p (X*q) r + value R p q (X*r) = 0 := by
  simp only [value_formula, split_X, rotate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem second_shift_invariant (p q r : Polynomial R) :
    value R (X^2*p) q r + value R p (X^2*q) r + value R p q (X^2*r) = 0 := by
  simp only [pow_two, mul_assoc, value_formula, split_X, rotate,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem euler_identity (p q r : Polynomial R) :
    value R (X*derivative p-p) q r + value R p (X*derivative q-q) r +
      value R p q (X*derivative r-r) = X*derivative (value R p q r)-3*value R p q r := by
  simp only [value_formula, split_euler, map_add, map_sub, derivative_mul]
  ring

theorem value_consecutive (n : ℕ) :
    value R (X^n) (X^(n+1)) (X^(n+2)) = X^(3*n+3) := by
  rw [value_formula, split_X_pow, split_X_pow, split_X_pow]
  have hb : n % 3 < 3 := Nat.mod_lt _ (by decide)
  generalize hn : n % 3 = r at hb ⊢
  interval_cases r <;>
    simp [monomialVector, Nat.add_mod, hn, ← pow_add] <;> congr 1 <;> omega

end Parafree.Linear.PolynomialCubic
