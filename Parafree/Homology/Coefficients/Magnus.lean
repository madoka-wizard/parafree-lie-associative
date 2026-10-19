import Parafree.Homology.Coefficients.FoxDimensionShift
import Parafree.Lie.ModuleExtension
import Parafree.Lie.Quotient

/-! The Magnus homomorphism to the split extension by free enveloping
coefficients. All formulas use the same derivative as the Fox exact sequence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Parafree.Homology.Coefficients.FoxSequence
open Parafree.Associative LieRings Parafree.Lie
open FreeAssociative
universe u
variable (R X : Type u) [CommRing R] (J : LieIdeal R (FreeLieAlgebra R X))

abbrev MagnusTarget := ModuleExtension (G R X J) (FreeCoefficients R X J)

def crossedDerivative : FreeLieAlgebra R X →ₗ[R] FreeCoefficients R X J :=
  (freeCoordinates R X J).symm.toLinearMap.comp
    ((familyProjection R X J).comp ((FreeAugmentation.derivative R X).comp
      (PBW.freeLieToFreeAlgebra R X).toLinearMap))

@[simp] theorem crossedDerivative_apply (z : FreeLieAlgebra R X) (i : X) :
    freeCoordinates R X J (crossedDerivative R X J z) i =
      projection R X J (FreeAugmentation.derivative R X (PBW.freeLieToFreeAlgebra R X z) i) := by
  change (freeCoordinates R X J ((freeCoordinates R X J).symm _)) i = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem crossedDerivative_lie (x y : FreeLieAlgebra R X) :
    crossedDerivative R X J ⁅x,y⁆ =
      ⁅quotientMk J x,crossedDerivative R X J y⁆ - ⁅quotientMk J y,crossedDerivative R X J x⁆ := by
  apply (freeCoordinates R X J).injective
  ext i
  rw [crossedDerivative_apply]
  rw [LieHom.map_lie,LieRing.of_associative_ring_bracket,
    FreeAugmentation.derivative_commutator R X _ _
      (augmentation_freeLie R X x) (augmentation_freeLie R X y)]
  change projection R X J (PBW.freeLieToFreeAlgebra R X x *
    FreeAugmentation.derivative R X (PBW.freeLieToFreeAlgebra R X y) i -
    PBW.freeLieToFreeAlgebra R X y * FreeAugmentation.derivative R X (PBW.freeLieToFreeAlgebra R X x) i) =
    UniversalEnvelopingAlgebra.ι R (quotientMk J x) * freeCoordinates R X J (crossedDerivative R X J y) i -
    UniversalEnvelopingAlgebra.ι R (quotientMk J y) * freeCoordinates R X J (crossedDerivative R X J x) i
  rw [map_sub,map_mul,map_mul,projection_lie,projection_lie,crossedDerivative_apply,crossedDerivative_apply]
  rfl

def magnus : FreeLieAlgebra R X →ₗ⁅R⁆ MagnusTarget R X J where
  toFun x := ⟨quotientMk J x,crossedDerivative R X J x⟩
  map_add' x y := by apply ModuleExtension.ext <;> exact map_add _ x y
  map_smul' c x := by apply ModuleExtension.ext <;> exact map_smul _ c x
  map_lie' {x y} := by
    apply ModuleExtension.ext
    · exact (quotientMk J).map_lie x y
    · exact crossedDerivative_lie R X J x y

@[simp] theorem magnus_base (x : FreeLieAlgebra R X) : (magnus R X J x).base = quotientMk J x := rfl
@[simp] theorem magnus_coefficient (x : FreeLieAlgebra R X) :
    (magnus R X J x).coefficient = crossedDerivative R X J x := rfl

theorem crossedDerivative_generator (i : X) :
    freeCoordinates R X J (crossedDerivative R X J (FreeLieAlgebra.of R i)) = Finsupp.single i 1 := by
  ext j
  rw [crossedDerivative_apply]
  simp only [PBW.freeLieToFreeAlgebra,FreeLieAlgebra.lift_of_apply]
  have hd : FreeAugmentation.derivative R X (FreeAlgebra.ι R i) = Finsupp.single i 1 := by
    simpa only [FreeAugmentation.concatenate_single,one_mul] using
      FreeAugmentation.derivative_concatenate_single R X i 1
  rw [hd]
  classical
  by_cases hij : i=j <;> simp [hij]

theorem crossedDerivative_relation (r : J) :
    freeCoordinates R X J (crossedDerivative R X J r) = fox R X J (Submodule.Quotient.mk r) := by
  ext i
  rw [crossedDerivative_apply,fox_mk_apply]
  rfl

theorem crossedDerivative_multiplication (x : FreeLieAlgebra R X) :
    concatenate R X J (freeCoordinates R X J (crossedDerivative R X J x)) =
      UniversalEnvelopingAlgebra.ι R (quotientMk J x) := by
  change concatenate R X J (freeCoordinates R X J ((freeCoordinates R X J).symm _)) = _
  rw [LinearEquiv.apply_symm_apply,LinearMap.comp_apply,LinearMap.comp_apply,projection_concatenate,
    FreeAugmentation.concatenate_derivative]
  change projection R X J (PBW.freeLieToFreeAlgebra R X x - algebraMap R (FreeAlgebra R X)
    (FreeAlgebra.algebraMapInv (PBW.freeLieToFreeAlgebra R X x))) = _
  rw [augmentation_freeLie,map_zero,sub_zero,projection_lie]
  rfl

end Parafree.Homology.Coefficients.FoxSequence
