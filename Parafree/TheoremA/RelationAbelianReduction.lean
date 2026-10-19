import Parafree.TheoremA.RelationReduction
import Parafree.TheoremA.RelationHomology
import Parafree.Lie.DerivedReduction

/-! Reduction commutes with abelianization of the actual relation ideal.
The comparison is built on integral representatives, including lifting every
field derived element; no flatness assumption is substituted for that step. -/

noncomputable section
namespace Parafree.TheoremA.Auxiliary

open Parafree.Linear

abbrev relationDerived (R : Type*) [CommRing R] : Submodule R (relationIdeal R) :=
  Parafree.Lie.derivedSubmodule R (relationIdeal R)

abbrev FieldRelationAbelianization :=
  LieRings.Homological.LieHomology.Abelianization (ZMod 2) (relationIdeal (ZMod 2))

theorem relationReduction_mem_derived {x : relationIdeal ℤ} (hx : x ∈ relationDerived ℤ) :
    relationReduction x ∈ relationDerived (ZMod 2) :=
  Parafree.Lie.integralMap_mem_derived relationReduction hx

/-- Every field derived element lifts to an integral derived element. -/
theorem relationDerived_lift {y : relationIdeal (ZMod 2)} (hy : y ∈ relationDerived (ZMod 2)) :
    ∃ x ∈ relationDerived ℤ, relationReduction x = y :=
  Parafree.Lie.integralMap_derived_lift relationReduction relationReduction_surjective hy

def relationAbelianReduction : RelationAbelianization →ₗ[ℤ] FieldRelationAbelianization :=
  Parafree.Lie.integralAbelianMap (p := 2) relationReduction

@[simp] theorem relationAbelianReduction_mk (x : relationIdeal ℤ) :
    relationAbelianReduction (Submodule.Quotient.mk x) =
      (relationDerived (ZMod 2)).mkQ (relationReduction x) := rfl

theorem relationAbelianReduction_surjective : Function.Surjective relationAbelianReduction :=
  Parafree.Lie.integralAbelianMap_surjective (p := 2) relationReduction relationReduction_surjective

theorem relationAbelianReduction_eq_zero_iff (x : RelationAbelianization) :
    relationAbelianReduction x = 0 ↔ ∃ y : RelationAbelianization, (2 : ℤ) • y = x :=
  Parafree.Lie.integralAbelianMap_eq_zero_iff (p := 2) relationReduction relationReduction_surjective
    relationReduction_eq_zero_iff x

/-- Abelianization comparison for the precise integral and field presentations. -/
def relationAbelianReductionEquiv : ModScalar.Quotient (2 : ℤ) RelationAbelianization ≃ₗ[ℤ]
    FieldRelationAbelianization :=
  equivOfCommonPresentation (ModScalar.mk (2 : ℤ) RelationAbelianization) relationAbelianReduction
    (ModScalar.mk_surjective (2 : ℤ) _) relationAbelianReduction_surjective (by
      ext x
      exact (ModScalar.mk_eq_zero (2 : ℤ) _ x).trans (relationAbelianReduction_eq_zero_iff x).symm)

theorem relationAbelianReductionEquiv_mk (x : RelationAbelianization) :
    relationAbelianReductionEquiv (ModScalar.mk (2 : ℤ) _ x) = relationAbelianReduction x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

/-- The comparison with the coefficient module in the checked Fox sequence. -/
def reducedRelationCoefficientEquiv : ModScalar.Quotient (2 : ℤ) RelationAbelianization ≃ₗ[ℤ]
    RelationCoefficients (ZMod 2) :=
  relationAbelianReductionEquiv.trans ((relationCoefficientEquiv (ZMod 2)).restrictScalars ℤ)

theorem reducedRelationCoefficientEquiv_mk (x : relationIdeal ℤ) :
    reducedRelationCoefficientEquiv (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk x)) =
      relationCoefficientEquiv (ZMod 2) (Submodule.Quotient.mk (relationReduction x)) := by
  change relationCoefficientEquiv (ZMod 2)
    (relationAbelianReductionEquiv (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk x))) = _
  rw [relationAbelianReductionEquiv_mk, relationAbelianReduction_mk]
  rfl

/-- Compatibility with the actual adjoint action, on all integral representatives. -/
theorem reducedRelationCoefficientEquiv_adjoint (x : Free ℤ) (j : relationIdeal ℤ) :
    reducedRelationCoefficientEquiv (ModScalar.mk (2 : ℤ) _
      (Submodule.Quotient.mk
        (Parafree.Homology.Coefficients.FoxSequence.adjoint ℤ (Fin 3) (relationIdeal ℤ) x j))) =
      ⁅(LieSubmodule.Quotient.mk (ambientReduction x) : Presented (ZMod 2)),
        reducedRelationCoefficientEquiv (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk j))⁆ := by
  simp only [reducedRelationCoefficientEquiv_mk]
  have had : relationReduction
      (Parafree.Homology.Coefficients.FoxSequence.adjoint ℤ (Fin 3) (relationIdeal ℤ) x j) =
      Parafree.Homology.Coefficients.FoxSequence.adjoint (ZMod 2) (Fin 3)
        (relationIdeal (ZMod 2)) (ambientReduction x) (relationReduction j) := by
    apply Subtype.ext
    exact ambientReduction.map_lie x (j : Free ℤ)
  rw [had]
  exact Parafree.Homology.Coefficients.FoxSequence.relationEquiv_adjoint
    (ZMod 2) (Fin 3) (relationIdeal (ZMod 2)) (ambientReduction x) (relationReduction j)

end Parafree.TheoremA.Auxiliary
