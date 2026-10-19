import Parafree.TheoremA.PositiveFreeExact
import Parafree.Lie.FreeModTwo

/-! The actual positive part of the reduced grading is a free Lie algebra over
the two-element field. This also supplies its vanishing second CE homology. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

abbrev FieldRelationFree := FreeLieAlgebra (ZMod 2) RelationBasisIndex

def fieldFreeHom : FieldRelationFree →ₗ⁅ZMod 2⁆ ReducedGraded :=
  FreeLieAlgebra.lift (ZMod 2) (fun i => freeGradedHom (FreeLieAlgebra.of ℤ i))

theorem fieldFreeHom_generatorMap (x : RelationFree) :
    fieldFreeHom (FreeScalarExtension.generatorMap (ZMod 2) RelationBasisIndex x) =
      freeGradedLinear x := by
  let f : FieldRelationFree →ₗ⁅ℤ⁆ ReducedGraded :=
    { fieldFreeHom.toLinearMap.restrictScalars ℤ with map_lie' := fieldFreeHom.map_lie _ _ }
  have h : f.comp (FreeScalarExtension.generatorMap (ZMod 2) RelationBasisIndex) =
      freeGradedHom := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change fieldFreeHom (FreeScalarExtension.generatorMap (ZMod 2) RelationBasisIndex
      (FreeLieAlgebra.of ℤ i)) = freeGradedHom (FreeLieAlgebra.of ℤ i)
    rw [FreeScalarExtension.generatorMap_of]
    exact FreeLieAlgebra.lift_of_apply _ _
  exact LieHom.congr_fun h x

theorem fieldFreeHom_injective : Function.Injective fieldFreeHom := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨a, rfl⟩ := FreeModTwo.generatorMap_surjective RelationBasisIndex x
  change fieldFreeHom (FreeScalarExtension.generatorMap (ZMod 2) RelationBasisIndex a) = 0 at hx
  rw [fieldFreeHom_generatorMap, freeGradedLinear_eq_zero_iff] at hx
  exact (FreeModTwo.generatorMap_eq_zero_iff RelationBasisIndex a).mpr hx

/-- Intrinsic characterization of the range inside the actual graded algebra. -/
theorem fieldFreeHom_range_iff (x : ReducedGraded) :
    x ∈ fieldFreeHom.range ↔ x 0 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := FreeModTwo.generatorMap_surjective RelationBasisIndex a
    exact (congrArg (fun x : ReducedGraded => x 0) (fieldFreeHom_generatorMap b)).trans
      (freeGradedLinear_zero b)
  · intro h
    obtain ⟨a, rfl⟩ := (freeGradedLinear_range_iff x).mpr h
    exact ⟨FreeScalarExtension.generatorMap (ZMod 2) RelationBasisIndex a,
      fieldFreeHom_generatorMap a⟩

abbrev PositiveAlgebra := fieldFreeHom.range

/-- This is an equivalence with the positive part of the actual reduction,
not merely an abstract free model with the same dimensions. -/
def positiveFreeEquiv : FieldRelationFree ≃ₗ⁅ZMod 2⁆ PositiveAlgebra :=
  fieldFreeHom.equivRangeOfInjective fieldFreeHom_injective

/-- Vanishing for the actual positive subalgebra, transported along the proved
free Lie equivalence. -/
theorem positiveHomologyTwo_subsingleton :
    Subsingleton (LieRings.Homological.LieHomology.Homology
      (R := ZMod 2) (L := PositiveAlgebra) 2) := by
  letI := LieRings.Homological.LieHomology.homologyTwo_free_subsingleton
    (ZMod 2) RelationBasisIndex
  exact (Parafree.Homology.lieEquivHomology positiveFreeEquiv 2).symm.injective.subsingleton

end Parafree.TheoremA.RationalModel
