import Parafree.TheoremB.RelationReduction
import Parafree.TheoremB.RelationHomology
import Parafree.Lie.DerivedReduction

/-! Reduction commutes with abelianization of the actual relation ideal.
The comparison is built on integral representatives, including lifting every
field derived element; no flatness assumption is substituted for that step. -/

noncomputable section
namespace Parafree.TheoremB.Auxiliary

open Parafree.Linear

abbrev RelationAbelianization := LieRings.Homological.LieHomology.Abelianization ℤ (relationIdeal ℤ)

abbrev relationDerived (R : Type*) [CommRing R] : Submodule R (relationIdeal R) :=
  Parafree.Lie.derivedSubmodule R (relationIdeal R)

abbrev FieldRelationAbelianization :=
  LieRings.Homological.LieHomology.Abelianization (ZMod 5) (relationIdeal (ZMod 5))

theorem relationReduction_mem_derived {x : relationIdeal ℤ} (hx : x ∈ relationDerived ℤ) :
    relationReduction x ∈ relationDerived (ZMod 5) :=
  Parafree.Lie.integralMap_mem_derived relationReduction hx

/-- Every field derived element lifts to an integral derived element. -/
theorem relationDerived_lift {y : relationIdeal (ZMod 5)} (hy : y ∈ relationDerived (ZMod 5)) :
    ∃ x ∈ relationDerived ℤ, relationReduction x = y :=
  Parafree.Lie.integralMap_derived_lift relationReduction relationReduction_surjective hy

def relationAbelianReduction : RelationAbelianization →ₗ[ℤ] FieldRelationAbelianization :=
  Parafree.Lie.integralAbelianMap (p := 5) relationReduction

@[simp] theorem relationAbelianReduction_mk (x : relationIdeal ℤ) :
    relationAbelianReduction (Submodule.Quotient.mk x) =
      (relationDerived (ZMod 5)).mkQ (relationReduction x) := rfl

theorem relationAbelianReduction_surjective : Function.Surjective relationAbelianReduction :=
  Parafree.Lie.integralAbelianMap_surjective (p := 5) relationReduction relationReduction_surjective

theorem relationAbelianReduction_eq_zero_iff (x : RelationAbelianization) :
    relationAbelianReduction x = 0 ↔ ∃ y : RelationAbelianization, (5 : ℤ) • y = x :=
  Parafree.Lie.integralAbelianMap_eq_zero_iff (p := 5) relationReduction relationReduction_surjective
    relationReduction_eq_zero_iff x

/-- Abelianization comparison for the precise integral and field presentations. -/
def relationAbelianReductionEquiv : ModScalar.Quotient (5 : ℤ) RelationAbelianization ≃ₗ[ℤ]
    FieldRelationAbelianization :=
  equivOfCommonPresentation (ModScalar.mk (5 : ℤ) RelationAbelianization) relationAbelianReduction
    (ModScalar.mk_surjective (5 : ℤ) _) relationAbelianReduction_surjective (by
      ext x
      exact (ModScalar.mk_eq_zero (5 : ℤ) _ x).trans (relationAbelianReduction_eq_zero_iff x).symm)

theorem relationAbelianReductionEquiv_mk (x : RelationAbelianization) :
    relationAbelianReductionEquiv (ModScalar.mk (5 : ℤ) _ x) = relationAbelianReduction x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

/-- The comparison with the coefficient module in the checked Fox sequence. -/
def reducedRelationCoefficientEquiv : ModScalar.Quotient (5 : ℤ) RelationAbelianization ≃ₗ[ℤ]
    RelationCoefficients :=
  relationAbelianReductionEquiv.trans ((relationCoefficientEquiv).restrictScalars ℤ)

theorem reducedRelationCoefficientEquiv_mk (x : relationIdeal ℤ) :
    reducedRelationCoefficientEquiv (ModScalar.mk (5 : ℤ) _ (Submodule.Quotient.mk x)) =
      relationCoefficientEquiv (Submodule.Quotient.mk (relationReduction x)) := by
  change relationCoefficientEquiv
    (relationAbelianReductionEquiv (ModScalar.mk (5 : ℤ) _ (Submodule.Quotient.mk x))) = _
  rw [relationAbelianReductionEquiv_mk, relationAbelianReduction_mk]
  rfl

/-- Compatibility with the actual adjoint action, on all integral representatives. -/
theorem reducedRelationCoefficientEquiv_adjoint (x : Free ℤ) (j : relationIdeal ℤ) :
    reducedRelationCoefficientEquiv (ModScalar.mk (5 : ℤ) _
      (Submodule.Quotient.mk
        (Parafree.Homology.Coefficients.FoxSequence.adjoint ℤ (Fin 2) (relationIdeal ℤ) x j))) =
      ⁅(LieSubmodule.Quotient.mk (ambientReduction x) : Presented (ZMod 5)),
        reducedRelationCoefficientEquiv (ModScalar.mk (5 : ℤ) _ (Submodule.Quotient.mk j))⁆ := by
  simp only [reducedRelationCoefficientEquiv_mk]
  have had : relationReduction
      (Parafree.Homology.Coefficients.FoxSequence.adjoint ℤ (Fin 2) (relationIdeal ℤ) x j) =
      Parafree.Homology.Coefficients.FoxSequence.adjoint (ZMod 5) (Fin 2)
        (relationIdeal (ZMod 5)) (ambientReduction x) (relationReduction j) := by
    apply Subtype.ext
    exact ambientReduction.map_lie x (j : Free ℤ)
  rw [had]
  exact Parafree.Homology.Coefficients.FoxSequence.relationEquiv_adjoint
    (ZMod 5) (Fin 2) (relationIdeal (ZMod 5)) (ambientReduction x) (relationReduction j)

end Parafree.TheoremB.Auxiliary
