import Parafree.TheoremA.SplitData
import Parafree.Homology.SplitExtension.Comparison

/-! The complete Theorem A for the specified six-generator presentation and
its actual residual quotient.  All comparisons are proved in the imported
modules; no homology computation is assumed here. -/

noncomputable section
namespace Parafree.TheoremA

open LieRings.Homological.LieHomology
open scoped TensorProduct

namespace RationalModel

def splitExtensionData : Parafree.Homology.SplitExtension.Data (ZMod 2)
    (Auxiliary.Presented (ZMod 2)) ReducedGraded (Auxiliary.RelationCoefficients (ZMod 2)) where
  ideal := positiveIdeal
  base := presentedSection
  quotient := presentedProjection
  part := positivePart
  quotient_base := presentedProjection_section
  quotient_ideal := presentedProjection_positive
  part_base := positivePart_section
  part_ideal := positivePart_positive
  decomposition := split_decomposition
  projection := positiveProjection
  coefficientSection := positiveSection
  projection_section := positiveProjection_section
  projection_ker := positiveProjection_eq_zero_iff
  section_equivariant := positiveSection_equivariant

/-- Second homology of the actual reduced grading. -/
def gradedHomologyTwoEquiv : Homology (R := ZMod 2) (L := ReducedGraded) 2 ≃ₗ[ZMod 2] ZMod 2 := by
  letI := Auxiliary.homologyTwo_subsingleton (ZMod 2)
  letI : Subsingleton (Homology (R := ZMod 2) (L := splitExtensionData.ideal) 2) :=
    positiveIdealHomologyTwo_subsingleton
  exact splitExtensionData.homologyTwoEquivOne.trans (Auxiliary.relationHomologyOneEquiv (ZMod 2))

end RationalModel

/-- The second CE homology of the actual reduction of the residual quotient. -/
def actualModTwoHomologyEquiv : Homology (R := ZMod 2) (L := LmodTwo) 2 ≃ₗ[ZMod 2] ZMod 2 :=
  (RationalModel.gradedHomologyEquiv 2).symm.trans RationalModel.gradedHomologyTwoEquiv

/-- The scalar factor is first so that its field-linear structure is explicit. -/
def homologyTwoTensorEquiv :
    (ZMod 2 ⊗[ℤ] Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod 2] ZMod 2 :=
  RationalModel.homologyTwoTensorGradedEquiv.trans RationalModel.gradedHomologyTwoEquiv

/-- The tensor order used in the manuscript, as an isomorphism of abelian groups. -/
def homologyTwoTensorRightEquiv :
    (Homology (R := ℤ) (L := L) 2 ⊗[ℤ] ZMod 2) ≃ₗ[ℤ] ZMod 2 :=
  ((TensorProduct.comm ℤ _ _).toAddEquiv.trans homologyTwoTensorEquiv.toAddEquiv).toIntLinearEquiv

/-- Both assertions of Theorem A in the current manuscript. -/
theorem theoremA :
    Parafree.Lie.IsParafree L 3 ∧ Parafree.Lie.IsParaEquivalence freeToL ∧
    Nonempty ((ZMod 2 ⊗[ℤ] Homology (R := ℤ) (L := L) 2) ≃ₗ[ZMod 2] ZMod 2) :=
  ⟨theoremA_part_one.1, theoremA_part_one.2, ⟨homologyTwoTensorEquiv⟩⟩

end Parafree.TheoremA
