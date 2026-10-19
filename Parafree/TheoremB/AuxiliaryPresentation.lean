import Parafree.TheoremB.AuxiliaryModel
import Parafree.Lie.Quotient
import Mathlib.Algebra.Lie.Free

/-! The two original relators present the explicit polynomial solvable algebra,
over every commutative ring in which six has an inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.Auxiliary
open Parafree.Lie
open Parafree.Lie.PolynomialSolvable
open Parafree.Lie.PolynomialSolvable.Algebra
variable (R : Type*) [CommRing R]

abbrev Free := FreeLieAlgebra R (Fin 2)
def generator (i : Fin 2) : Free R := FreeLieAlgebra.of R i
def relator : Fin 2 → Free R :=
  ![f₁ (generator R 0) (generator R 1), f₂ (generator R 0) (generator R 1)]
def relationIdeal : LieIdeal R (Free R) :=
  LieSubmodule.lieSpan R (Free R) (Set.range (relator R))
abbrev Presented := Free R ⧸ relationIdeal R
def gen (i : Fin 2) : Presented R := quotientMk (relationIdeal R) (generator R i)

theorem relator_zero (i : Fin 2) : quotientMk (relationIdeal R) (relator R i) = 0 :=
  (quotientMk_eq_zero _ _).mpr (LieSubmodule.subset_lieSpan (Set.mem_range_self i))

theorem presented_f₁ : f₁ (gen R 0) (gen R 1) = 0 := by
  have h := relator_zero R 0
  simpa only [relator, Matrix.cons_val_zero, f₁, w, map_sub, LieHom.map_lie,
    map_zsmul, gen] using h

theorem presented_f₂ : f₂ (gen R 0) (gen R 1) = 0 := by
  have hh := relator_zero R 1
  simpa only [relator, Matrix.cons_val_one, Matrix.cons_val_zero, f₂, h, c, w,
    map_sub, LieHom.map_lie, map_zsmul, gen] using hh

variable {R} (q : R) (hq : (6:R)*q = 1)

def freeEvaluation : Free R →ₗ⁅R⁆ G q :=
  FreeLieAlgebra.lift R ![T R (-9*q), a₀ q]

@[simp] theorem freeEvaluation_generator (i : Fin 2) :
    freeEvaluation q (generator R i) = ![T R (-9*q),a₀ q] i :=
  FreeLieAlgebra.lift_of_apply _ i

def toG : Presented R →ₗ⁅R⁆ G q :=
  quotientLift (relationIdeal R) (freeEvaluation q) (by
    apply LieSubmodule.lieSpan_le.mpr
    rintro _ ⟨i,rfl⟩
    change freeEvaluation q (relator R i) = 0
    fin_cases i
    · change freeEvaluation q (f₁ (generator R 0) (generator R 1)) = 0
      simpa only [f₁, w, map_sub, LieHom.map_lie,
        map_zsmul, freeEvaluation_generator, Matrix.cons_val_one] using f₁_zero q hq
    · change freeEvaluation q (f₂ (generator R 0) (generator R 1)) = 0
      simpa only [f₂, h, c, w,
        map_sub, LieHom.map_lie, map_zsmul, freeEvaluation_generator] using f₂_zero q hq)

@[simp] theorem toG_gen (i : Fin 2) :
    toG q hq (gen R i) = ![T R (-9*q),a₀ q] i := freeEvaluation_generator q i

def fromG : G q →ₗ⁅R⁆ Presented R :=
  (liftData q hq (gen R 0) (gen R 1) (presented_f₁ R) (presented_f₂ R)).hom

@[simp] theorem fromG_T : fromG q hq (T R (-9*q)) = gen R 0 := by
  exact (liftData q hq (gen R 0) (gen R 1) (presented_f₁ R) (presented_f₂ R)).hom_T
@[simp] theorem fromG_S : fromG q hq (S R (-9*q)) = WeightRelations.s (gen R 0) (gen R 1) := by
  exact (liftData q hq (gen R 0) (gen R 1) (presented_f₁ R) (presented_f₂ R)).hom_S
@[simp] theorem fromG_E : fromG q hq (E R (-9*q)) = WeightRelations.e (gen R 0) (gen R 1) := by
  exact (liftData q hq (gen R 0) (gen R 1) (presented_f₁ R) (presented_f₂ R)).hom_E
@[simp] theorem fromG_M (n : ℕ) : fromG q hq (M R (-9*q) n) =
    SolvableRelations.monomial (WeightRelations.s (gen R 0) (gen R 1))
      (WeightRelations.m (gen R 0) (gen R 1)) n := by
  rw [M, fromG, LiftData.hom_polynomial]
  exact polynomialFamily_X_pow (R := R) (SolvableRelations.monomial (WeightRelations.s (gen R 0) (gen R 1))
    (WeightRelations.m (gen R 0) (gen R 1))) n

@[simp] theorem toG_s : toG q hq (WeightRelations.s (gen R 0) (gen R 1)) = S R (-9*q) := by
  simpa only [WeightRelations.s, w, map_sub, map_neg, map_zsmul, LieHom.map_lie,
    toG_gen, Matrix.cons_val_zero, Matrix.cons_val_one] using weight_s q hq
@[simp] theorem toG_e : toG q hq (WeightRelations.e (gen R 0) (gen R 1)) = E R (-9*q) := by
  simpa only [WeightRelations.e, map_sub, LieHom.map_lie,
    toG_gen, Matrix.cons_val_zero, Matrix.cons_val_one] using weight_e q hq
@[simp] theorem toG_m : toG q hq (WeightRelations.m (gen R 0) (gen R 1)) = M R (-9*q) 0 := by
  simpa only [WeightRelations.m, w, map_sub, map_zsmul, LieHom.map_lie,
    toG_gen, Matrix.cons_val_zero, Matrix.cons_val_one] using weight_m q hq

theorem to_from : (toG q hq).comp (fromG q hq) = LieHom.id := by
  apply PolynomialSolvable.hom_ext
  · simp
  · simp
  · simp
  · intro n
    change toG q hq (fromG q hq (M R (-9*q) n)) = M R (-9*q) n
    rw [fromG_M]
    induction n with
    | zero => exact toG_m q hq
    | succ n ih => rw [SolvableRelations.monomial_succ, LieHom.map_lie, toG_s, ih, S_M]

theorem from_to : (fromG q hq).comp (toG q hq) = LieHom.id := by
  apply quotient_hom_ext
  apply FreeLieAlgebra.hom_ext
  intro i
  change fromG q hq (toG q hq (gen R i)) = gen R i
  rw [toG_gen]
  fin_cases i
  · exact fromG_T q hq
  · change fromG q hq (a₀ q) = gen R 1
    rw [a₀, map_smul, map_add, map_add, map_smul, map_smul, fromG_S, fromG_E, fromG_M]
    simp only [SolvableRelations.monomial_zero]
    have hg := WeightRelations.generators_identity (gen R 0) (gen R 1)
    have hg' : (3:R) • WeightRelations.s (gen R 0) (gen R 1) +
        (2:R) • WeightRelations.e (gen R 0) (gen R 1) + WeightRelations.m (gen R 0) (gen R 1) =
        (6:R) • gen R 1 := by simpa only [← Int.cast_smul_eq_zsmul R, Int.cast_ofNat] using hg
    rw [hg', smul_smul, mul_comm q 6, hq, one_smul]

/-- Proposition `g` of the manuscript, with the exact generator assignment. -/
def equivG : Presented R ≃ₗ⁅R⁆ G q :=
  LieEquiv.ofBijective (toG q hq)
    ⟨Function.LeftInverse.injective (show Function.LeftInverse (fromG q hq)
        (toG q hq) from fun x => DFunLike.congr_fun (from_to q hq) x),
      Function.RightInverse.surjective (show Function.RightInverse (fromG q hq)
        (toG q hq) from fun x => DFunLike.congr_fun (to_from q hq) x)⟩

include hq in
theorem presented_free : Module.Free R (Presented R) :=
  Module.Free.of_equiv (equivG q hq).symm.toLinearEquiv

end Parafree.TheoremB.Auxiliary
