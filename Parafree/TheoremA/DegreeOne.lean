import Parafree.TheoremA.ZeroDegree
import Parafree.TheoremA.RelationAbelianReduction

/-! Identify degree one of the actual grading with the computed Fox coefficient
module, and embed that module equivariantly into the split Lie algebra. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

/-- Degree one before quotienting is exactly the integral relation ideal. -/
def relationOneTermEquiv : Auxiliary.relationIdeal ℤ ≃ₗ[ℤ] dividedFiltration 1 :=
  (Submodule.topEquiv : (⊤ : Submodule ℤ (Auxiliary.relationIdeal ℤ)) ≃ₗ[ℤ]
    Auxiliary.relationIdeal ℤ).symm.trans (relationTermEquiv 0)

def relationOnePresentation : Auxiliary.relationIdeal ℤ →ₗ[ℤ] IntegralLayer 1 :=
  (integralLayerRelations 1).mkQ.comp relationOneTermEquiv.toLinearMap

theorem relationOnePresentation_ker :
    LinearMap.ker relationOnePresentation = relationDerived ℤ := by
  ext x
  change (integralLayerRelations 1).mkQ (relationOneTermEquiv x) = 0 ↔ x ∈ relationDerived ℤ
  exact (Submodule.Quotient.mk_eq_zero _).trans
    (relationTerm_next_iff 0 ⟨x, LieSubmodule.mem_top _⟩)

def abelianIntegralLayerEquiv : RelationAbelianization ≃ₗ[ℤ] IntegralLayer 1 :=
  equivOfCommonPresentation (relationDerived ℤ).mkQ relationOnePresentation
    (Submodule.mkQ_surjective _)
    ((integralLayerRelations 1).mkQ_surjective.comp relationOneTermEquiv.surjective)
    ((Submodule.ker_mkQ _).trans relationOnePresentation_ker.symm)

theorem abelianIntegralLayerEquiv_mk (x : Auxiliary.relationIdeal ℤ) :
    abelianIntegralLayerEquiv (Submodule.Quotient.mk x) =
      (integralLayerRelations 1).mkQ (relationOneTermEquiv x) :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

def abelianReducedLayerEquiv : ModScalar.Quotient (2 : ℤ) RelationAbelianization ≃ₗ[ℤ]
    ReducedLayer 1 :=
  (ModScalar.congr (2 : ℤ) abelianIntegralLayerEquiv).trans
    (ModScalar.quotientReductionEquiv (2 : ℤ) (integralLayerRelations 1))

theorem abelianReducedLayerEquiv_mk (x : Auxiliary.relationIdeal ℤ) :
    abelianReducedLayerEquiv (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk x)) =
      (reducedLayerRelations 1).mkQ (relationOneTermEquiv x) := by
  change ModScalar.quotientReductionEquiv (2 : ℤ) (integralLayerRelations 1)
    (ModScalar.mk (2 : ℤ) _ (abelianIntegralLayerEquiv (Submodule.Quotient.mk x))) = _
  rw [abelianIntegralLayerEquiv_mk, ModScalar.quotientReductionEquiv_mk]
  rfl

def coefficientLayerEquiv : RelationCoefficients (ZMod 2) ≃ₗ[ℤ] ReducedLayer 1 :=
  reducedRelationCoefficientEquiv.symm.trans abelianReducedLayerEquiv

def coefficientInclusionIntegral : RelationCoefficients (ZMod 2) →ₗ[ℤ] ReducedGraded :=
  (DFinsupp.lsingle 1).comp coefficientLayerEquiv.toLinearMap

def coefficientInclusion : RelationCoefficients (ZMod 2) →ₗ[ZMod 2] ReducedGraded :=
  coefficientInclusionIntegral.toAddMonoidHom.toZModLinearMap 2

abbrev integralCoefficient (j : Auxiliary.relationIdeal ℤ) : RelationCoefficients (ZMod 2) :=
  reducedRelationCoefficientEquiv (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk j))

theorem coefficientInclusion_integral (j : Auxiliary.relationIdeal ℤ) :
    coefficientInclusion (integralCoefficient j) = gradedClass 1 (relationOneTermEquiv j) := by
  change (DFinsupp.single 1 (abelianReducedLayerEquiv
    (reducedRelationCoefficientEquiv.symm (reducedRelationCoefficientEquiv
      (ModScalar.mk (2 : ℤ) _ (Submodule.Quotient.mk j))))) : ReducedGraded) = _
  rw [LinearEquiv.symm_apply_apply, abelianReducedLayerEquiv_mk]
  rfl

theorem integralCoefficient_surjective : Function.Surjective integralCoefficient := by
  intro v
  obtain ⟨a, rfl⟩ := reducedRelationCoefficientEquiv.surjective v
  obtain ⟨b, rfl⟩ := ModScalar.mk_surjective (2 : ℤ) _ a
  obtain ⟨j, rfl⟩ := (relationDerived ℤ).mkQ_surjective b
  exact ⟨j, rfl⟩

theorem coefficientInclusion_injective : Function.Injective coefficientInclusion := by
  intro v w h
  apply coefficientLayerEquiv.injective
  have he := congrArg (fun x : ReducedGraded => x 1) h
  change (DFinsupp.single 1 (coefficientLayerEquiv v) : ReducedGraded) 1 =
    (DFinsupp.single 1 (coefficientLayerEquiv w) : ReducedGraded) 1 at he
  simpa only [DFinsupp.single_eq_same] using he

theorem coefficientInclusion_positive (v : RelationCoefficients (ZMod 2)) :
    coefficientInclusion v ∈ positiveIdeal := by
  obtain ⟨j, rfl⟩ := integralCoefficient_surjective v
  rw [coefficientInclusion_integral, mem_positiveIdeal]
  exact DFinsupp.single_eq_of_ne (by decide : 0 ≠ 1)

/-- The actual section from the presented auxiliary algebra. -/
def presentedSection : Presented (ZMod 2) →ₗ⁅ZMod 2⁆ ReducedGraded :=
  zeroDegreeSection.comp (equivCrossProduct (ZMod 2)).toLieHom

theorem fieldEvaluation_reduction (x : Auxiliary.Free ℤ) :
    freeEvaluation (ZMod 2) (ambientReduction x) = freeFieldEvaluation x := by
  let f : Auxiliary.Free (ZMod 2) →ₗ⁅ℤ⁆ CrossProduct (ZMod 2) :=
    { (freeEvaluation (ZMod 2)).toLinearMap.restrictScalars ℤ with
      map_lie' := (freeEvaluation (ZMod 2)).map_lie _ _ }
  have h : f.comp ambientReduction = freeFieldEvaluation := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change freeEvaluation (ZMod 2) (ambientReduction (generator ℤ i)) =
      freeFieldEvaluation (generator ℤ i)
    rw [ambientReduction_generator, freeEvaluation_generator, freeFieldEvaluation_generator]
  exact LieHom.congr_fun h x

theorem presentedSection_reduction (x : Auxiliary.Free ℤ) :
    presentedSection (quotientMk (Auxiliary.relationIdeal (ZMod 2)) (ambientReduction x)) =
      zeroClassHom x := by
  change zeroDegreeSection (freeEvaluation (ZMod 2) (ambientReduction x)) = _
  rw [fieldEvaluation_reduction, zeroDegreeSection_evaluation]

/-- Equivariance is checked using the actual mixed graded bracket and the Fox
adjoint formula, not imposed as a transported module structure. -/
theorem coefficientInclusion_lie_integral (x : Auxiliary.Free ℤ) (j : Auxiliary.relationIdeal ℤ) :
    ⁅zeroClassHom x, coefficientInclusion (integralCoefficient j)⁆ =
      coefficientInclusion
        ⁅(LieSubmodule.Quotient.mk (ambientReduction x) : Presented (ZMod 2)), integralCoefficient j⁆ := by
  rw [← reducedRelationCoefficientEquiv_adjoint, coefficientInclusion_integral,
    coefficientInclusion_integral]
  change ⁅gradedClass 0 ⟨x, Submodule.mem_top⟩, gradedClass 1 (relationOneTermEquiv j)⁆ = _
  rw [gradedClass_lie]
  rfl

theorem coefficientInclusion_equivariant (x : Presented (ZMod 2))
    (v : RelationCoefficients (ZMod 2)) :
    ⁅presentedSection x, coefficientInclusion v⁆ = coefficientInclusion ⁅x, v⁆ := by
  obtain ⟨a, rfl⟩ := quotientMk_surjective (Auxiliary.relationIdeal (ZMod 2)) x
  obtain ⟨b, rfl⟩ := FreeModTwo.generatorMap_surjective (Fin 3) a
  obtain ⟨j, rfl⟩ := integralCoefficient_surjective v
  rw [presentedSection_reduction]
  exact coefficientInclusion_lie_integral b j

end Parafree.TheoremA.RationalModel
