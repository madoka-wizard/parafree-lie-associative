import Parafree.TheoremB.MagnusReduction
import Parafree.TheoremB.TransferTarget
import Parafree.TheoremB.FiniteGeneration

/-! The concrete transfer data for the exact Lie subring of Theorem B.
The retraction comes from the localized Magnus representation and its
residue-field coordinates; the section divides integral relations by five. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.TheoremB.ConcreteTransfer
open Parafree.Lie Parafree.Linear Parafree.Homology.Coefficients Auxiliary
open scoped TensorProduct
abbrev K := ZMod 5
abbrev G := Presented K
abbrev V := MagnusReduction.V
abbrev E := MagnusReduction.E

def integral : P →ₗ⁅ℤ⁆ E := MagnusReduction.hom.comp IntegralMagnus.hom

def reduced : PmodFive →ₗ⁅K⁆ E := ScalarExtension.lift K integral

@[simp] theorem reduced_reduction (x : P) : reduced (reduction x) = integral x := by
  change (1:K) • integral x = _
  exact one_smul _ _

theorem reduced_integralLift (x : IntegralFree) :
    reduced (reduction (DividedModel.integralLift x)) =
      ⟨quotientMk (relationIdeal K) (ambientReduction x),0⟩ := by
  rw [reduced_reduction]
  change MagnusReduction.hom (IntegralMagnus.hom (DividedModel.integralLift x)) = _
  rw [IntegralMagnus.hom_integralLift,MagnusReduction.hom_scaled]
  rfl

theorem reduced_divide (r : relationIdeal ℤ) :
    reduced (reduction (DividedModel.divide r)) =
      ⟨0,(relationCoefficientEquiv (Submodule.Quotient.mk (relationReduction r)) : V)⟩ := by
  rw [reduced_reduction]
  change MagnusReduction.hom (IntegralMagnus.hom (DividedModel.divide r)) = _
  rw [IntegralMagnus.hom_divide,MagnusReduction.hom_relationImage,MagnusReduction.fieldIntegral_relation]

theorem reduced_base (g : G) : reduced (auxiliaryBase g) = ⟨g,0⟩ := by
  have he : reduced.comp auxiliaryBase = ModuleExtension.inclusion K G V := by
    apply Auxiliary.hom_ext
    intro i
    change reduced (auxiliaryBase (gen K i)) = ⟨gen K i,0⟩
    have h := reduced_integralLift (Auxiliary.generator ℤ i)
    rw [← auxiliaryBase_integral] at h
    simpa only [ambientReduction_generator] using h
  exact LieHom.congr_fun he g

theorem reduced_section (v : RelationCoefficients) :
    reduced (coefficientSection v) = ⟨0,(v:V)⟩ := by
  obtain ⟨q,rfl⟩ := reducedRelationCoefficientEquiv.surjective v
  obtain ⟨a,rfl⟩ := ModScalar.mk_surjective (5:ℤ) RelationAbelianization q
  obtain ⟨r,rfl⟩ := (relationDerived ℤ).mkQ_surjective a
  change reduced (coefficientSection (reducedRelationCoefficientEquiv
    (ModScalar.mk (5:ℤ) _ (Submodule.Quotient.mk r)))) = _
  rw [coefficientSection_mk]
  change reduced (reduction (DividedModel.divide r)) = _
  rw [reduced_divide]
  apply ModuleExtension.ext
  · rfl
  · have he := congrArg (fun v : RelationCoefficients => (v:V)) (reducedRelationCoefficientEquiv_mk r)
    exact he.symm

/-- Intrinsic closure of the coefficient-kernel condition on the four-generator ring. -/
def goodIntegral : LieSubalgebra ℤ P where
  carrier := {x | (integral x).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)}
  zero_mem' := by change (integral 0).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K); rw [map_zero]; exact Submodule.zero_mem _
  add_mem' {x y} hx hy := by
    change (integral (x+y)).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
    rw [map_add]
    exact (FoxSequence.relations K (Fin 2) (relationIdeal K)).add_mem hx hy
  smul_mem' c x hx := by
    change (integral (c•x)).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
    rw [map_smul]
    exact (FoxSequence.relations K (Fin 2) (relationIdeal K)).toSubmodule.toAddSubgroup.zsmul_mem hx c
  lie_mem' {x y} hx hy := by
    change (integral ⁅x,y⁆).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
    rw [LieHom.map_lie]
    exact (FoxSequence.relations K (Fin 2) (relationIdeal K)).sub_mem
      ((FoxSequence.relations K (Fin 2) (relationIdeal K)).lie_mem hy)
      ((FoxSequence.relations K (Fin 2) (relationIdeal K)).lie_mem hx)

theorem integral_coefficient_mem (x : P) :
    (integral x).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K) := by
  have he : LieSubalgebra.lieSpan ℤ P (Set.range TheoremB.generator) ≤ goodIntegral := by
    apply LieSubalgebra.lieSpan_le.mpr
    rintro _ ⟨i,rfl⟩
    change (MagnusReduction.hom (IntegralMagnus.hom (TheoremB.generator i))).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
    rw [IntegralMagnus.hom_generator]
    fin_cases i
    · change (MagnusReduction.hom (IntegralMagnus.scaled (Auxiliary.generator ℤ 0))).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
      rw [MagnusReduction.hom_scaled]
      exact Submodule.zero_mem _
    · change (MagnusReduction.hom (IntegralMagnus.scaled (Auxiliary.generator ℤ 1))).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
      rw [MagnusReduction.hom_scaled]
      exact Submodule.zero_mem _
    · change (MagnusReduction.hom (IntegralMagnus.relationImage (IntegralMagnus.integralRelator 0))).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
      rw [MagnusReduction.hom_relationImage,MagnusReduction.fieldIntegral_relation]
      exact (relationCoefficientEquiv (Submodule.Quotient.mk (relationReduction (IntegralMagnus.integralRelator 0)))).property
    · change (MagnusReduction.hom (IntegralMagnus.relationImage (IntegralMagnus.integralRelator 1))).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
      rw [MagnusReduction.hom_relationImage,MagnusReduction.fieldIntegral_relation]
      exact (relationCoefficientEquiv (Submodule.Quotient.mk (relationReduction (IntegralMagnus.integralRelator 1)))).property
  rw [generators_lieSpan] at he
  exact he (LieSubalgebra.mem_top x)

theorem reduced_coefficient_mem (x : PmodFive) :
    (reduced x).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy =>
    rw [map_add]
    exact (FoxSequence.relations K (Fin 2) (relationIdeal K)).add_mem hx hy
  | tmul c x =>
    change (c • integral x).coefficient ∈ FoxSequence.relations K (Fin 2) (relationIdeal K)
    exact (FoxSequence.relations K (Fin 2) (relationIdeal K)).smul_mem c (integral_coefficient_mem x)

def quotient : PmodFive →ₗ⁅K⁆ G := (ModuleExtension.projection K G V).comp reduced

def projection : PmodFive →ₗ[K] RelationCoefficients :=
  ((ModuleExtension.coefficientMap K G V).comp reduced.toLinearMap).codRestrict _ reduced_coefficient_mem

def data : TransferData where
  base := auxiliaryBase
  quotient := quotient
  coefficientSection := coefficientSection
  projection := projection
  quotient_base g := congrArg ModuleExtension.base (reduced_base g)
  quotient_section v := congrArg ModuleExtension.base (reduced_section v)
  projection_section v := Subtype.ext (congrArg ModuleExtension.coefficient (reduced_section v))
  section_equivariant := coefficientSection_equivariant
  projection_lie x y := by
    apply Subtype.ext
    exact congrArg ModuleExtension.coefficient (reduced.map_lie x y)

end Parafree.TheoremB.ConcreteTransfer
