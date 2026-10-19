import Parafree.Homology.Coefficients.FreeAssociative
import LieRings.PBW.Reduction

/-! Restrict the free associative augmentation sequence to any ideal of the
free Lie algebra. No freeness assertion about the ideal as a Lie algebra is used. -/

noncomputable section

namespace Parafree.Homology.Coefficients.FreeAssociative

universe u
variable (R X : Type u) [CommRing R]

theorem augmentation_freeLie (x : FreeLieAlgebra R X) :
    FreeAlgebra.algebraMapInv (LieRings.PBW.freeLieToFreeAlgebra R X x) = 0 := by
  have h : ((FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R).toLieHom).comp
      (LieRings.PBW.freeLieToFreeAlgebra R X) = 0 := by
    apply FreeLieAlgebra.hom_ext
    intro i
    simp [LieRings.PBW.freeLieToFreeAlgebra, FreeAlgebra.algebraMapInv]
  exact congrArg (fun g : FreeLieAlgebra R X →ₗ⁅R⁆ R => g x) h

/-- The left action of a relation ideal on the free associative algebra. -/
def idealAction (J : LieIdeal R (FreeLieAlgebra R X)) : J →ₗ⁅R⁆ FreeAlgebra R X :=
  (LieRings.PBW.freeLieToFreeAlgebra R X).comp J.incl

theorem augmentation_idealAction (J : LieIdeal R (FreeLieAlgebra R X)) (x : J) :
    FreeAlgebra.algebraMapInv (idealAction R X J x) = 0 :=
  augmentation_freeLie R X x

/-- The actual restricted free associative sequence, on all CE chain groups. -/
theorem ideal_sequence_shortExact (J : LieIdeal R (FreeLieAlgebra R X)) :
    (sequence (inclusion (idealAction R X J))
      (augmentation (idealAction R X J) (augmentation_idealAction R X J))
      (inclusion_augmentation_zero (idealAction R X J)
        (augmentation_idealAction R X J))).ShortExact :=
  sequence_shortExact (idealAction R X J) (augmentation_idealAction R X J)

end Parafree.Homology.Coefficients.FreeAssociative
