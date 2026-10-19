import Parafree.Lie.PolynomialSolvable

/-! Universal maps from the polynomial solvable algebra, expressed in terms of
an abelian polynomial family and three operators. -/

noncomputable section

namespace Parafree.Lie.PolynomialSolvable
open Polynomial Algebra
variable {R : Type*} [CommRing R] {k : R}
variable {L : Type*} [LieRing L] [LieAlgebra R L]

structure LiftData where
  t : L
  s : L
  e : L
  family : Polynomial R →ₗ[R] L
  family_commute : ∀ p q, ⁅family p, family q⁆ = 0
  s_family : ∀ p, ⁅s, family p⁆ = family (X*p)
  e_family : ∀ p, ⁅e, family p⁆ = k • family (X^2*p)
  t_family : ∀ p, ⁅t, family p⁆ = family (X*derivative p-p)
  s_e : ⁅s,e⁆ = 0
  t_s : ⁅t,s⁆ = s
  t_e : ⁅t,e⁆ = (2:R) • e

namespace LiftData
variable (d : LiftData (R := R) (k := k) (L := L))

def linear : Algebra R k →ₗ[R] L where
  toFun z := d.family z.poly + z.shift • d.s + z.second • d.e + z.weight • d.t
  map_add' x y := by simp only [add_poly, add_shift, add_second, add_weight,
    map_add, add_smul]; module
  map_smul' r x := by simp only [smul_poly, smul_shift, smul_second, smul_weight,
    map_smul, RingHom.id_apply]; module

theorem linear_lie (x y : Algebra R k) : d.linear ⁅x,y⁆ = ⁅d.linear x,d.linear y⁆ := by
  have hps (p) : ⁅d.family p,d.s⁆ = -d.family (X*p) := by
    rw [← lie_skew, d.s_family]
  have hpe (p) : ⁅d.family p,d.e⁆ = -(k • d.family (X^2*p)) := by
    rw [← lie_skew, d.e_family]
  have hpt (p) : ⁅d.family p,d.t⁆ = -d.family (X*derivative p-p) := by
    rw [← lie_skew, d.t_family]
  have hes : ⁅d.e,d.s⁆ = 0 := by rw [← lie_skew, d.s_e, neg_zero]
  have hst : ⁅d.s,d.t⁆ = -d.s := by rw [← lie_skew, d.t_s]
  have het : ⁅d.e,d.t⁆ = -((2:R) • d.e) := by rw [← lie_skew, d.t_e]
  simp only [linear, LinearMap.coe_mk, AddHom.coe_mk, lie_poly, lie_shift,
    lie_second, lie_weight, add_mul, ← smul_eq_C_mul, smul_mul_assoc,
    map_add, map_sub, map_smul, add_lie, lie_add, smul_lie, lie_smul,
    d.family_commute, d.s_family, d.e_family, d.t_family, d.s_e, d.t_s, d.t_e,
    hps, hpe, hpt, hes, hst, het, lie_self]
  module

def hom : Algebra R k →ₗ⁅R⁆ L := { d.linear with map_lie' := d.linear_lie _ _ }

@[simp] theorem hom_polynomial (p : Polynomial R) : d.hom (polynomial R k p) = d.family p := by
  simp [hom, linear, polynomial]
@[simp] theorem hom_S : d.hom (S R k) = d.s := by simp [hom, linear, S]
@[simp] theorem hom_E : d.hom (E R k) = d.e := by simp [hom, linear, E]
@[simp] theorem hom_T : d.hom (T R k) = d.t := by simp [hom, linear, T]

end LiftData
end Parafree.Lie.PolynomialSolvable
