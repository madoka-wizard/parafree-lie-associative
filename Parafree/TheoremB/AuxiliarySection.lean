import Parafree.TheoremB.ModFiveHomology
import Parafree.TheoremB.AuxiliaryCoefficients

/-! The canonical map from the auxiliary presentation to the actual reduction.
Both original relators vanish because they are five times the divided generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB
open Parafree.Lie
open scoped TensorProduct

abbrev reduction : P →ₗ⁅ℤ⁆ PmodFive := FreeScalarExtension.unit (ZMod 5)

theorem reduction_f₁ : f₁ (reduction t) (reduction a) = 0 := by
  rw [← map_f₁,← five_u,map_zsmul,← Int.cast_smul_eq_zsmul (ZMod 5)]
  rw [show ((5:ℤ):ZMod 5) = 0 by decide,zero_smul]

theorem reduction_f₂ : f₂ (reduction t) (reduction a) = 0 := by
  rw [← map_f₂,← five_v,map_zsmul,← Int.cast_smul_eq_zsmul (ZMod 5)]
  rw [show ((5:ℤ):ZMod 5) = 0 by decide,zero_smul]

def auxiliaryFreeMap : Auxiliary.Free (ZMod 5) →ₗ⁅ZMod 5⁆ PmodFive :=
  FreeLieAlgebra.lift (ZMod 5) ![reduction t,reduction a]

@[simp] theorem auxiliaryFreeMap_generator (i : Fin 2) :
    auxiliaryFreeMap (Auxiliary.generator (ZMod 5) i) = ![reduction t,reduction a] i :=
  FreeLieAlgebra.lift_of_apply _ i

theorem auxiliaryFreeMap_relator (i : Fin 2) :
    auxiliaryFreeMap (Auxiliary.relator (ZMod 5) i) = 0 := by
  fin_cases i
  · change auxiliaryFreeMap (f₁ (Auxiliary.generator (ZMod 5) 0) (Auxiliary.generator (ZMod 5) 1)) = 0
    simpa only [f₁,w,map_sub,
      LieHom.map_lie,map_zsmul,auxiliaryFreeMap_generator,Matrix.cons_val_zero,Matrix.cons_val_one] using reduction_f₁
  · change auxiliaryFreeMap (f₂ (Auxiliary.generator (ZMod 5) 0) (Auxiliary.generator (ZMod 5) 1)) = 0
    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,f₂,h,c,w,
      map_sub,LieHom.map_lie,map_zsmul,auxiliaryFreeMap_generator] using reduction_f₂

def auxiliaryBase : Auxiliary.Presented (ZMod 5) →ₗ⁅ZMod 5⁆ PmodFive :=
  quotientLift (Auxiliary.relationIdeal (ZMod 5)) auxiliaryFreeMap
    (LieSubmodule.lieSpan_le.mpr (by rintro _ ⟨i,rfl⟩; exact auxiliaryFreeMap_relator i))

@[simp] theorem auxiliaryBase_gen (i : Fin 2) :
    auxiliaryBase (Auxiliary.gen (ZMod 5) i) = ![reduction t,reduction a] i :=
  auxiliaryFreeMap_generator i

end Parafree.TheoremB
