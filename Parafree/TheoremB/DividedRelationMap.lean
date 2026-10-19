import Parafree.TheoremB.IntegralRelations
import Parafree.TheoremB.AuxiliarySection
import Parafree.Lie.DerivedReduction

/-! The actual division-by-five map on the integral relation ideal.
It descends to the ideal's abelianization after reducing the target modulo
five, and is equivariant for the ambient free Lie action. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.DividedModel
open Parafree.Lie

abbrev I := Auxiliary.relationIdeal ℤ


def divide : I →ₗ[ℤ] P where
  toFun r := ⟨(1/5:ℚ) • inclusion r, divided_mem r⟩
  map_add' r s := by
    apply Subtype.ext
    change (1/5:ℚ) • inclusion ((r : IntegralFree)+(s : IntegralFree)) = _
    rw [map_add,smul_add]
    rfl
  map_smul' c r := by
    apply Subtype.ext
    change (1/5:ℚ) • inclusion (c • (r : IntegralFree)) = c • ((1/5:ℚ) • inclusion r)
    rw [map_smul,smul_comm]

@[simp] theorem divide_coe (r : I) : (divide r : Ambient) = (1/5:ℚ) • inclusion r := rfl

theorem five_divide (r : I) : (5:ℤ) • divide r = integralLift r := by
  apply Subtype.ext
  change (5:ℤ) • ((1/5:ℚ) • inclusion r) = (integralLift r : Ambient)
  rw [integralLift_coe,← Int.cast_smul_eq_zsmul ℚ,smul_smul]
  norm_num

def adjoint (x : IntegralFree) (r : I) : I := ⟨⁅x,(r : IntegralFree)⁆,I.lie_mem r.property⟩

theorem divide_adjoint (x : IntegralFree) (r : I) :
    divide (adjoint x r) = ⁅integralLift x,divide r⁆ := by
  apply Subtype.ext
  change (1/5:ℚ) • inclusion ⁅x,(r : IntegralFree)⁆ = ⁅(integralLift x : Ambient),(divide r : Ambient)⁆
  rw [integralLift_coe,divide_coe,LieHom.map_lie,lie_smul]

theorem divide_bracket (r s : I) : divide ⁅r,s⁆ = (5:ℤ) • ⁅divide r,divide s⁆ := by
  apply Subtype.ext
  change (1/5:ℚ) • inclusion ⁅(r : IntegralFree),(s : IntegralFree)⁆ =
    (5:ℤ) • ⁅(1/5:ℚ) • inclusion r,(1/5:ℚ) • inclusion s⁆
  rw [LieHom.map_lie,smul_lie,lie_smul,← Int.cast_smul_eq_zsmul ℚ,smul_smul,smul_smul]
  norm_num

def reducedDivide : I →ₗ[ℤ] PmodFive := reduction.toLinearMap.comp divide

theorem reducedDivide_bracket (r s : I) : reducedDivide ⁅r,s⁆ = 0 := by
  change reduction (divide ⁅r,s⁆) = 0
  rw [divide_bracket,map_zsmul,← Int.cast_smul_eq_zsmul (ZMod 5)]
  rw [show ((5:ℤ):ZMod 5) = 0 by decide,zero_smul]

theorem reducedDivide_adjoint (x : IntegralFree) (r : I) :
    reducedDivide (adjoint x r) = ⁅reduction (integralLift x),reducedDivide r⁆ := by
  change reduction (divide (adjoint x r)) = ⁅reduction (integralLift x),reduction (divide r)⁆
  rw [divide_adjoint,LieHom.map_lie]

theorem derived_le_ker : derivedSubmodule ℤ I ≤ reducedDivide.ker := by
  rw [derivedSubmodule,LieSubmodule.lieIdeal_oper_eq_linear_span']
  apply Submodule.span_le.mpr
  rintro _ ⟨r,_,s,_,rfl⟩
  exact reducedDivide_bracket r s

def abelianDivide : LieRings.Homological.LieHomology.Abelianization ℤ I →ₗ[ℤ] PmodFive :=
  (derivedSubmodule ℤ I).liftQ reducedDivide derived_le_ker

@[simp] theorem abelianDivide_mk (r : I) : abelianDivide (Submodule.Quotient.mk r) = reducedDivide r := rfl

theorem abelianDivide_adjoint (x : IntegralFree) (r : I) :
    abelianDivide (Submodule.Quotient.mk (adjoint x r)) =
      ⁅reduction (integralLift x),abelianDivide (Submodule.Quotient.mk r)⁆ :=
  reducedDivide_adjoint x r

end Parafree.TheoremB.DividedModel
