import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Lie.Basic
import Mathlib.Tactic

/-! A polynomial abelian ideal with two commuting shift actions and an Euler
weight derivation. The coefficient of the second shift is arbitrary. -/

namespace Parafree.Lie.PolynomialSolvable

open Polynomial

noncomputable section

variable (R : Type*) [CommRing R] (k : R)

@[ext] structure Algebra (k : R) where
  poly : Polynomial R
  shift : R
  second : R
  weight : R

namespace Algebra

variable {R k}

def coordinates : Algebra R k ≃ Polynomial R × R × R × R where
  toFun x := (x.poly, x.shift, x.second, x.weight)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (Algebra R k) := coordinates.addCommGroup
instance : Module R (Algebra R k) := coordinates.module R

def coordinatesLinear : Algebra R k ≃ₗ[R] Polynomial R × R × R × R where
  __ := coordinates
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem zero_poly : (0 : Algebra R k).poly = 0 := rfl
@[simp] theorem zero_shift : (0 : Algebra R k).shift = 0 := rfl
@[simp] theorem zero_second : (0 : Algebra R k).second = 0 := rfl
@[simp] theorem zero_weight : (0 : Algebra R k).weight = 0 := rfl
@[simp] theorem add_poly (x y : Algebra R k) : (x+y).poly = x.poly+y.poly := rfl
@[simp] theorem add_shift (x y : Algebra R k) : (x+y).shift = x.shift+y.shift := rfl
@[simp] theorem add_second (x y : Algebra R k) : (x+y).second = x.second+y.second := rfl
@[simp] theorem add_weight (x y : Algebra R k) : (x+y).weight = x.weight+y.weight := rfl
@[simp] theorem smul_poly (r : R) (x : Algebra R k) : (r • x).poly = r • x.poly := rfl
@[simp] theorem smul_shift (r : R) (x : Algebra R k) : (r • x).shift = r*x.shift := rfl
@[simp] theorem smul_second (r : R) (x : Algebra R k) : (r • x).second = r*x.second := rfl
@[simp] theorem smul_weight (r : R) (x : Algebra R k) : (r • x).weight = r*x.weight := rfl

instance : Bracket (Algebra R k) (Algebra R k) where
  bracket x y := ⟨
    (C x.shift * X + C (k*x.second) * X^2) * y.poly -
      (C y.shift * X + C (k*y.second) * X^2) * x.poly +
      C x.weight * (X * derivative y.poly - y.poly) -
      C y.weight * (X * derivative x.poly - x.poly),
    x.weight*y.shift - y.weight*x.shift,
    2*(x.weight*y.second - y.weight*x.second), 0⟩

@[simp] theorem lie_poly (x y : Algebra R k) :
    ⁅x,y⁆.poly = (C x.shift * X + C (k*x.second) * X^2) * y.poly -
      (C y.shift * X + C (k*y.second) * X^2) * x.poly +
      C x.weight * (X * derivative y.poly - y.poly) -
      C y.weight * (X * derivative x.poly - x.poly) := rfl
@[simp] theorem lie_shift (x y : Algebra R k) :
    ⁅x,y⁆.shift = x.weight*y.shift - y.weight*x.shift := rfl
@[simp] theorem lie_second (x y : Algebra R k) :
    ⁅x,y⁆.second = 2*(x.weight*y.second - y.weight*x.second) := rfl
@[simp] theorem lie_weight (x y : Algebra R k) : ⁅x,y⁆.weight = 0 := rfl

instance : LieRing (Algebra R k) where
  add_lie x y z := by
    apply Algebra.ext <;> simp only [add_poly, add_shift, add_second, add_weight, lie_poly,
      lie_shift, lie_second, lie_weight, map_add, mul_add] <;> ring
  lie_add x y z := by
    apply Algebra.ext <;> simp only [add_poly, add_shift, add_second, add_weight, lie_poly,
      lie_shift, lie_second, lie_weight, map_add, mul_add] <;> ring
  lie_self x := by apply Algebra.ext <;> simp
  leibniz_lie x y z := by
    apply Algebra.ext <;> simp only [add_poly, add_shift, add_second, add_weight, lie_poly,
      lie_shift, lie_second, lie_weight, map_add, map_sub, map_mul, map_ofNat,
      map_zero, Nat.cast_ofNat, derivative_mul, derivative_C, derivative_X, derivative_pow] <;> ring

instance : LieAlgebra R (Algebra R k) where
  lie_smul r x y := by
    apply Algebra.ext <;> simp only [smul_poly, smul_shift, smul_second, smul_weight, lie_poly,
      lie_shift, lie_second, lie_weight, map_mul, smul_eq_C_mul, derivative_mul, derivative_C] <;> ring

variable (R k) in
instance : Module.Free R (Algebra R k) :=
  Module.Free.of_equiv (coordinatesLinear (R := R) (k := k)).symm

variable (R k) in
def polynomial : Polynomial R →ₗ[R] Algebra R k where
  toFun p := ⟨p, 0, 0, 0⟩
  map_add' _ _ := by apply Algebra.ext <;> simp
  map_smul' _ _ := by apply Algebra.ext <;> simp

variable (R k) in
def S : Algebra R k := ⟨0, 1, 0, 0⟩
variable (R k) in
def E : Algebra R k := ⟨0, 0, 1, 0⟩
variable (R k) in
def T : Algebra R k := ⟨0, 0, 0, 1⟩
variable (R k) in
def M (n : ℕ) : Algebra R k := polynomial R k (X^n)

@[simp] theorem polynomial_lie (p q : Polynomial R) :
    ⁅polynomial R k p, polynomial R k q⁆ = 0 := by
  apply Algebra.ext <;> simp [polynomial]

@[simp] theorem S_polynomial (p : Polynomial R) :
    ⁅S R k, polynomial R k p⁆ = polynomial R k (X*p) := by
  apply Algebra.ext <;> simp [S, polynomial]

@[simp] theorem E_polynomial (p : Polynomial R) :
    ⁅E R k, polynomial R k p⁆ = polynomial R k (C k*X^2*p) := by
  apply Algebra.ext <;> simp [E, polynomial]

@[simp] theorem T_polynomial (p : Polynomial R) :
    ⁅T R k, polynomial R k p⁆ = polynomial R k (X*derivative p-p) := by
  apply Algebra.ext <;> simp [T, polynomial]

@[simp] theorem S_E : ⁅S R k, E R k⁆ = 0 := by
  apply Algebra.ext <;> simp [S, E]
@[simp] theorem T_S : ⁅T R k, S R k⁆ = S R k := by
  apply Algebra.ext <;> simp [T, S]
@[simp] theorem T_E : ⁅T R k, E R k⁆ = (2:R) • E R k := by
  apply Algebra.ext <;> simp [T, E]

@[simp] theorem M_lie (i j : ℕ) : ⁅M R k i, M R k j⁆ = 0 := polynomial_lie _ _
@[simp] theorem S_M (n : ℕ) : ⁅S R k, M R k n⁆ = M R k (n+1) := by
  simp [M, pow_succ', S_polynomial]
@[simp] theorem E_M (n : ℕ) : ⁅E R k, M R k n⁆ = k • M R k (n+2) := by
  simp only [M, E_polynomial, ← map_smul]
  apply congrArg (polynomial R k)
  simp only [smul_eq_C_mul, pow_add]
  ring
@[simp] theorem T_M (n : ℕ) : ⁅T R k, M R k n⁆ = ((n:R)-1) • M R k n := by
  simp only [M, T_polynomial, ← map_smul]
  apply congrArg (polynomial R k)
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_X_pow_succ]
    simp only [smul_eq_C_mul, map_sub, map_one, Nat.cast_add, Nat.cast_one, pow_succ]
    ring

theorem decomposition (z : Algebra R k) :
    z = polynomial R k z.poly + z.shift • S R k + z.second • E R k + z.weight • T R k := by
  apply Algebra.ext <;> simp [polynomial, S, E, T]

end Algebra
end
end Parafree.Lie.PolynomialSolvable
