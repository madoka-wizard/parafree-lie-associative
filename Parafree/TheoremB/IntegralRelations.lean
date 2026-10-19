import Parafree.TheoremB.Model
import Parafree.TheoremB.AuxiliaryPresentation
import Parafree.Lie.DividedIdeal

/-! Integral and divided relation maps into the original rational subring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.DividedModel
open Parafree.Lie

def inclusion : IntegralFree →ₗ⁅ℤ⁆ Ambient := FreeScalarExtension.generatorMap ℚ (Fin 2)

@[simp] theorem inclusion_generator (i : Fin 2) :
    inclusion (Auxiliary.generator ℤ i) = FreeLieAlgebra.of ℚ i :=
  FreeScalarExtension.generatorMap_of ℚ (Fin 2) i

@[simp] theorem inclusion_relator (i : Fin 2) :
    inclusion (Auxiliary.relator ℤ i) = ![f₁ ambientT ambientA,f₂ ambientT ambientA] i := by
  fin_cases i
  · change inclusion (f₁ (Auxiliary.generator ℤ 0) (Auxiliary.generator ℤ 1)) = f₁ ambientT ambientA
    rw [map_f₁,inclusion_generator,inclusion_generator]
    rfl
  · change inclusion (f₂ (Auxiliary.generator ℤ 0) (Auxiliary.generator ℤ 1)) = f₂ ambientT ambientA
    rw [map_f₂,inclusion_generator,inclusion_generator]
    rfl

def integralLift : IntegralFree →ₗ⁅ℤ⁆ P := FreeLieAlgebra.lift ℤ ![t,a]

theorem integralLift_coe (z : IntegralFree) : (integralLift z : Ambient) = inclusion z := by
  have he : algebra.incl.comp integralLift = inclusion := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change (integralLift (FreeLieAlgebra.of ℤ i) : Ambient) = inclusion (FreeLieAlgebra.of ℤ i)
    rw [show integralLift (FreeLieAlgebra.of ℤ i) = ![t,a] i from FreeLieAlgebra.lift_of_apply _ _,
      show inclusion (FreeLieAlgebra.of ℤ i) = FreeLieAlgebra.of ℚ i from inclusion_generator i]
    fin_cases i <;> rfl
  exact LieHom.congr_fun he z


theorem integral_mem (x : IntegralFree) : inclusion x ∈ algebra :=
  integralLift_coe x ▸ (integralLift x).property

/-- Direct ideal induction suffices; no higher divided powers are needed. -/
theorem divided_mem (r : Auxiliary.relationIdeal ℤ) : (1/5:ℚ) • inclusion r ∈ algebra := by
  apply smul_map_mem_of_lieSpan inclusion (1/5:ℚ) algebra (Auxiliary.relator ℤ) integral_mem
    (hx := r.property)
  intro i
  rw [inclusion_relator]
  fin_cases i
  · exact (u : P).property
  · exact (v : P).property

end Parafree.TheoremB.DividedModel
