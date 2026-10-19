import Parafree.TheoremA.DegreeOne

/-! The actual abelianization of the positive free ideal is the Fox coefficient
module.  The projection and its equivariant section are given by degree one. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

def coefficientProjectionIntegral : ReducedGraded →ₗ[ℤ] RelationCoefficients (ZMod 2) :=
  coefficientLayerEquiv.symm.toLinearMap.comp (DFinsupp.lapply 1)

def coefficientProjection : ReducedGraded →ₗ[ZMod 2] RelationCoefficients (ZMod 2) :=
  coefficientProjectionIntegral.toAddMonoidHom.toZModLinearMap 2

@[simp] theorem coefficientProjection_inclusion (v : RelationCoefficients (ZMod 2)) :
    coefficientProjection (coefficientInclusion v) = v := by
  change coefficientLayerEquiv.symm
    ((DFinsupp.single 1 (coefficientLayerEquiv v) : ReducedGraded) 1) = v
  rw [DFinsupp.single_eq_same, LinearEquiv.symm_apply_apply]

theorem coefficientProjection_eq_zero (x : ReducedGraded) :
    coefficientProjection x = 0 ↔ x 1 = 0 := by
  change coefficientLayerEquiv.symm (x 1) = 0 ↔ x 1 = 0
  exact coefficientLayerEquiv.symm.map_eq_zero_iff

def positiveProjection : positiveIdeal →ₗ[ZMod 2] RelationCoefficients (ZMod 2) :=
  coefficientProjection.comp positiveIdeal.toSubmodule.subtype

def positiveSection : RelationCoefficients (ZMod 2) →ₗ[ZMod 2] positiveIdeal :=
  coefficientInclusion.codRestrict positiveIdeal.toSubmodule coefficientInclusion_positive

@[simp] theorem positiveProjection_section (v : RelationCoefficients (ZMod 2)) :
    positiveProjection (positiveSection v) = v := coefficientProjection_inclusion v

def integralPositiveHom : RelationFree →ₗ⁅ℤ⁆ positiveIdeal where
  toFun x := ⟨freeGradedLinear x, (mem_positiveIdeal _).mpr (freeGradedLinear_zero x)⟩
  map_add' x y := Subtype.ext (map_add freeGradedLinear x y)
  map_smul' c x := Subtype.ext (map_smul freeGradedLinear c x)
  map_lie' {x y} := Subtype.ext (freeGradedLinear_lie x y)

theorem integralPositiveHom_surjective : Function.Surjective integralPositiveHom := by
  intro x
  obtain ⟨a, ha⟩ := (freeGradedLinear_range_iff x).mpr ((mem_positiveIdeal x).mp x.property)
  exact ⟨a, Subtype.ext ha⟩

theorem freeGradedLinear_one_of_derived {x : RelationFree}
    (hx : x ∈ derivedSubmodule ℤ RelationFree) : freeGradedLinear x 1 = 0 := by
  rw [freeGradedLinear_component 0,
    FreeHomogeneous.homogeneousComponent_eq_zero_of_lowerCentral RelationBasisIndex 1 x hx,
    map_zero, map_zero]

/-- Vanishing degree one is exactly membership in the intrinsic commutator. -/
theorem positiveProjection_eq_zero_iff (x : positiveIdeal) :
    positiveProjection x = 0 ↔ x ∈ derivedSubmodule (ZMod 2) positiveIdeal := by
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := integralPositiveHom_surjective x
    have ha : freeGradedLinear a 1 = 0 := (coefficientProjection_eq_zero _).mp hx
    have hcomponent : ModScalar.mk (2 : ℤ) _
        ((FreeHomogeneous.sumEquiv RelationBasisIndex).symm a 1) = 0 := by
      apply (positiveLayerEquiv 0).injective
      rw [map_zero, ← freeGradedLinear_component]
      exact ha
    obtain ⟨b, hb⟩ := (ModScalar.mk_eq_zero (2 : ℤ) _ _).mp hcomponent
    have hproj : (2 : ℤ) • (b : RelationFree) =
        FreeHomogeneous.projection RelationBasisIndex 1 a := congrArg Subtype.val hb
    have hd : a - (2 : ℤ) • (b : RelationFree) ∈ derivedSubmodule ℤ RelationFree := by
      rw [hproj]
      exact FreeHomogeneous.sub_projection_mem RelationBasisIndex 0 ⟨a, LieSubmodule.mem_top _⟩
    have he : integralPositiveHom (a - (2 : ℤ) • (b : RelationFree)) = integralPositiveHom a := by
      apply Subtype.ext
      change freeGradedLinear (a - (2 : ℤ) • (b : RelationFree)) = freeGradedLinear a
      rw [map_sub, (freeGradedLinear_eq_zero_iff ((2 : ℤ) • (b : RelationFree))).mpr ⟨b, rfl⟩, sub_zero]
    rw [← he]
    exact integralMap_mem_derived integralPositiveHom hd
  · intro hx
    obtain ⟨a, ha, rfl⟩ := integralMap_derived_lift integralPositiveHom integralPositiveHom_surjective hx
    apply (coefficientProjection_eq_zero _).mpr
    exact freeGradedLinear_one_of_derived ha

theorem positiveProjection_ker : LinearMap.ker positiveProjection =
    derivedSubmodule (ZMod 2) positiveIdeal := by
  ext x
  exact positiveProjection_eq_zero_iff x

/-- This is the abelianization of the actual positive ideal, with the already
computed coefficient module as codomain. -/
def positiveAbelianizationEquiv :
    LieRings.Homological.LieHomology.Abelianization (ZMod 2) positiveIdeal ≃ₗ[ZMod 2]
      RelationCoefficients (ZMod 2) :=
  equivOfCommonPresentation (derivedSubmodule (ZMod 2) positiveIdeal).mkQ positiveProjection
    (Submodule.mkQ_surjective _) (fun v => ⟨positiveSection v, positiveProjection_section v⟩)
    ((Submodule.ker_mkQ _).trans positiveProjection_ker.symm)

@[simp] theorem positiveAbelianizationEquiv_mk (x : positiveIdeal) :
    positiveAbelianizationEquiv (Submodule.Quotient.mk x) = positiveProjection x :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

end Parafree.TheoremA.RationalModel
