import Parafree.TheoremA.PositiveAbelianization
import Parafree.Lie.DerivedStable

/-! The actual split extension, with the Fox module as the equivariantly split
abelianization of its free kernel. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie
open Auxiliary

theorem positiveSection_equivariant (g : Presented (ZMod 2))
    (v : RelationCoefficients (ZMod 2)) :
    ⁅presentedSection g, positiveSection v⁆ = positiveSection ⁅g,v⁆ := by
  apply Subtype.ext
  exact coefficientInclusion_equivariant g v

theorem positiveProjection_equivariant (g : Presented (ZMod 2)) (f : positiveIdeal) :
    positiveProjection ⁅presentedSection g,f⁆ = ⁅g,positiveProjection f⁆ :=
  projection_equivariant_of_section positiveIdeal presentedSection positiveProjection positiveSection
    positiveProjection_section positiveProjection_eq_zero_iff positiveSection_equivariant g f

def presentedProjection : ReducedGraded →ₗ⁅ZMod 2⁆ Presented (ZMod 2) :=
  (equivCrossProduct (ZMod 2)).symm.toLieHom.comp zeroDegreeMap

@[simp] theorem presentedProjection_section (g : Presented (ZMod 2)) :
    presentedProjection (presentedSection g) = g := by
  change (equivCrossProduct (ZMod 2)).symm
    (zeroDegreeMap (zeroDegreeSection (equivCrossProduct (ZMod 2) g))) = g
  rw [zeroDegreeMap_apply_section, LieEquiv.symm_apply_apply]

@[simp] theorem presentedProjection_positive (f : positiveIdeal) :
    presentedProjection f = 0 := by
  change (equivCrossProduct (ZMod 2)).symm (zeroDegreeMap f) = 0
  rw [zeroDegreeMap_positive, map_zero]

def positivePart : ReducedGraded →ₗ[ZMod 2] positiveIdeal :=
  (LinearMap.snd (ZMod 2) (CrossProduct (ZMod 2)) positiveIdeal).comp splitLinearEquiv.toLinearMap

theorem split_decomposition (x : ReducedGraded) :
    x = presentedSection (presentedProjection x) + (positivePart x : ReducedGraded) := by
  change x = zeroDegreeSection
    (equivCrossProduct (ZMod 2) ((equivCrossProduct (ZMod 2)).symm (zeroDegreeMap x))) +
      (x - zeroDegreeSection (zeroDegreeMap x))
  rw [LieEquiv.apply_symm_apply]
  abel

@[simp] theorem positivePart_section (g : Presented (ZMod 2)) :
    positivePart (presentedSection g) = 0 := by
  apply Subtype.ext
  change zeroDegreeSection (equivCrossProduct (ZMod 2) g) -
    zeroDegreeSection (zeroDegreeMap (zeroDegreeSection (equivCrossProduct (ZMod 2) g))) = 0
  rw [zeroDegreeMap_apply_section, sub_self]

@[simp] theorem positivePart_positive (f : positiveIdeal) : positivePart f = f := by
  apply Subtype.ext
  change (f : ReducedGraded) - zeroDegreeSection (zeroDegreeMap f) = f
  rw [zeroDegreeMap_positive, map_zero, sub_zero]

end Parafree.TheoremA.RationalModel
