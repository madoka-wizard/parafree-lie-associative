import Parafree.Linear.PolynomialCubic
import Parafree.Homology.DegreeThreeWedges
import Parafree.Homology.Concrete

/-! Polynomial-valued cubic cochains for the solvable polynomial model.
The only remaining boundary term is the weight operator on the determinant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.Homology.PolynomialCubic
open Polynomial LieRings.Homological.LieHomology
open Parafree.Lie.PolynomialSolvable
open Parafree.Linear.PolynomialCubic
variable (R : Type*) [CommRing R] (k : R)

def polyProjection : Algebra R k →ₗ[R] Polynomial R where
  toFun := Algebra.poly
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def cochain : (⋀[R]^3 (Algebra R k)) →ₗ[R] Polynomial R :=
  exteriorPower.alternatingMapLinearEquiv ((form R).compLinearMap (polyProjection R k))

@[simp] theorem cochain_wedge (x y z : Algebra R k) :
    cochain R k (exteriorPower.ιMulti R 3 ![x,y,z]) = value R x.poly y.poly z.poly := by
  simp only [cochain, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  change form R ((polyProjection R k) ∘ ![x,y,z]) = form R ![x.poly,y.poly,z.poly]
  congr 1
  funext i
  fin_cases i <;> rfl

def weight (p : Polynomial R) : Polynomial R := X * derivative p - 3*p

theorem boundary_formula (x y z w : Algebra R k) :
    cochain R k (differential R (Algebra R k) 3 (exteriorPower.ιMulti R 4 ![x,y,z,w])) =
      -x.weight • weight R (value R y.poly z.poly w.poly) +
       y.weight • weight R (value R x.poly z.poly w.poly) -
       z.weight • weight R (value R x.poly y.poly w.poly) +
       w.weight • weight R (value R x.poly y.poly z.poly) := by
  rw [differential_three_wedge]
  simp only [map_add, map_sub, map_neg, cochain_wedge]
  simp only [value_formula, Algebra.lie_poly, add_mul, mul_assoc,
    split_C_mul, map_add, map_sub, Pi.add_apply, Pi.sub_apply, smul_eq_C_mul]
  simp only [split_X_derivative]
  simp only [split_X, pow_two, mul_assoc, rotate,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    weight, derivative_mul, map_add, map_sub, map_neg]
  ring

theorem weight_coeff (p : Polynomial R) (n : ℕ) :
    (weight R p).coeff n = ((n:R)-3)*p.coeff n := by
  cases n with
  | zero => simp [weight]
  | succ n =>
    simp only [weight, coeff_sub, coeff_X_mul, coeff_derivative,
      Nat.cast_add, Nat.cast_one]
    rw [show (3:Polynomial R) = C (3:R) from (map_ofNat C 3).symm, coeff_C_mul]
    ring

/-- Taking a coefficient whose weight is zero annihilates every CE boundary. -/
theorem coefficient_cocycle (n : ℕ) (hn : (n:R)-3 = 0) :
    ((Polynomial.lcoeff R n).comp (cochain R k)).comp (differential R (Algebra R k) 3) = 0 := by
  apply exteriorPower.linearMap_ext
  ext v
  have hv : v = ![v 0,v 1,v 2,v 3] := by funext i; fin_cases i <;> rfl
  rw [hv]
  change (cochain R k (differential R (Algebra R k) 3 (exteriorPower.ιMulti R 4
    ![v 0,v 1,v 2,v 3]))).coeff n = 0
  rw [boundary_formula]
  simp only [coeff_add, coeff_sub, coeff_smul,
    smul_eq_mul, weight_coeff, hn, zero_mul, mul_zero, add_zero, sub_zero]

def evaluate (n : ℕ) (hn : (n:R)-3 = 0) :
    Homology (R := R) (L := Algebra R k) 3 →ₗ[R] R :=
  Concrete.evaluate R (Algebra R k) 2 ((Polynomial.lcoeff R n).comp (cochain R k))
    (coefficient_cocycle R k n hn)

end Parafree.Homology.PolynomialCubic
