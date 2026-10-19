import Parafree.TheoremB.RelationAbelianReduction
import Parafree.TheoremB.DividedRelationMap

/-! The relation coefficient module maps into the actual reduction by dividing
integral representatives by five. The comparison retains its adjoint action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB
open Parafree.Lie Parafree.Linear Auxiliary

namespace DividedModel

def reducedAbelianDivide : ModScalar.Quotient (5:ℤ) RelationAbelianization →ₗ[ℤ] PmodFive :=
  (ModScalar.multiples (5:ℤ) RelationAbelianization).liftQ abelianDivide (by
    rintro _ ⟨x,rfl⟩
    change abelianDivide ((5:ℤ) • x) = 0
    rw [map_smul,← Int.cast_smul_eq_zsmul (ZMod 5)]
    rw [show ((5:ℤ):ZMod 5) = 0 by decide,zero_smul])

@[simp] theorem reducedAbelianDivide_mk (r : I) :
    reducedAbelianDivide (ModScalar.mk (5:ℤ) _ (Submodule.Quotient.mk r)) = reducedDivide r := rfl

end DividedModel

/-- The section candidate, defined on the actual Fox coefficient module. -/
def coefficientSection : RelationCoefficients →ₗ[ZMod 5] PmodFive :=
  (DividedModel.reducedAbelianDivide.comp reducedRelationCoefficientEquiv.symm.toLinearMap).toAddMonoidHom.toZModLinearMap 5

@[simp] theorem coefficientSection_mk (r : relationIdeal ℤ) :
    coefficientSection (reducedRelationCoefficientEquiv
      (ModScalar.mk (5:ℤ) _ (Submodule.Quotient.mk r))) = DividedModel.reducedDivide r := by
  change DividedModel.reducedAbelianDivide
    (reducedRelationCoefficientEquiv.symm (reducedRelationCoefficientEquiv _)) = _
  rw [LinearEquiv.symm_apply_apply,DividedModel.reducedAbelianDivide_mk]

theorem auxiliaryBase_integral (x : IntegralFree) :
    auxiliaryBase (quotientMk (relationIdeal (ZMod 5)) (ambientReduction x)) =
      reduction (DividedModel.integralLift x) := by
  let f : Free (ZMod 5) →ₗ⁅ℤ⁆ PmodFive :=
    { auxiliaryFreeMap.toLinearMap.restrictScalars ℤ with map_lie' := auxiliaryFreeMap.map_lie _ _ }
  have he : f.comp ambientReduction = reduction.comp DividedModel.integralLift := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change auxiliaryFreeMap (ambientReduction (Auxiliary.generator ℤ i)) =
      reduction (DividedModel.integralLift (Auxiliary.generator ℤ i))
    rw [ambientReduction_generator,auxiliaryFreeMap_generator]
    rw [show DividedModel.integralLift (Auxiliary.generator ℤ i) = ![t,a] i from FreeLieAlgebra.lift_of_apply _ _]
    fin_cases i <;> rfl
  exact LieHom.congr_fun he x

/-- Equivariance holds for every auxiliary element and every relation class. -/
theorem coefficientSection_equivariant (g : Presented (ZMod 5)) (v : RelationCoefficients) :
    ⁅auxiliaryBase g,coefficientSection v⁆ = coefficientSection ⁅g,v⁆ := by
  obtain ⟨g,rfl⟩ := quotientMk_surjective (relationIdeal (ZMod 5)) g
  obtain ⟨x,rfl⟩ := FreeModNat.generatorMap_surjective 5 (Fin 2) g
  obtain ⟨q,rfl⟩ := reducedRelationCoefficientEquiv.surjective v
  obtain ⟨a,rfl⟩ := ModScalar.mk_surjective (5:ℤ) RelationAbelianization q
  obtain ⟨r,rfl⟩ := (relationDerived ℤ).mkQ_surjective a
  change ⁅auxiliaryBase (quotientMk (relationIdeal (ZMod 5)) (ambientReduction x)),
    coefficientSection (reducedRelationCoefficientEquiv (ModScalar.mk (5:ℤ) _ (Submodule.Quotient.mk r)))⁆ = _
  rw [coefficientSection_mk,auxiliaryBase_integral]
  have he := congrArg coefficientSection (reducedRelationCoefficientEquiv_adjoint x r)
  rw [coefficientSection_mk] at he
  exact (DividedModel.reducedDivide_adjoint x r).symm.trans he

end Parafree.TheoremB
