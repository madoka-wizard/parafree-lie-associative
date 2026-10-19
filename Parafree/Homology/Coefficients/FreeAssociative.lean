import Parafree.Associative.FreeAugmentation
import Parafree.Homology.Coefficients.AssociativeRestriction
import Parafree.Homology.Coefficients.ExactSequence
import Parafree.Homology.Coefficients.Trivial

/-!
# The restricted free associative augmentation sequence

Any Lie algebra mapping into the augmentation ideal of a free associative
algebra acts by left multiplication. Last-letter decomposition gives a short
exact sequence of its coefficient CE complexes. The underlying linear
retraction is explicit and needs no flatness assumption on the Lie algebra.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.FreeAssociative

open Parafree.Associative

universe u
variable {R L X : Type u} [CommRing R] [LieRing L] [LieAlgebra R L]
variable (f : L →ₗ⁅R⁆ FreeAlgebra R X)
variable (haug : ∀ x, FreeAlgebra.algebraMapInv (f x) = 0)

abbrev Regular := AssociativeRestriction.Coefficients f (FreeAlgebra R X)
abbrev Generators := AssociativeRestriction.Coefficients f (X →₀ FreeAlgebra R X)

/-- Left-linear concatenation, restricted to the given Lie action. -/
def inclusion : Generators f →ₗ⁅R,L⁆ Regular f :=
  AssociativeRestriction.map f (FreeAugmentation.concatenate R X)

def augmentation : Regular f →ₗ⁅R,L⁆ Trivial R L :=
  { (TrivialLieModule.equiv R L R).symm.toLinearMap.comp
      ((FreeAlgebra.algebraMapInv : FreeAlgebra R X →ₐ[R] R).toLinearMap.comp
        (AssociativeRestriction.equiv f (FreeAlgebra R X)).toLinearMap) with
    map_lie' := by
      intro x a
      apply (TrivialLieModule.equiv R L R).injective
      change FreeAlgebra.algebraMapInv
        (f x * AssociativeRestriction.equiv f (FreeAlgebra R X) a) = 0
      rw [map_mul, haug, zero_mul] }

theorem inclusion_augmentation_zero : (augmentation f haug).comp (inclusion f) = 0 := by
  ext m
  apply (TrivialLieModule.equiv R L R).injective
  exact FreeAugmentation.augmentation_concatenate R X
    (AssociativeRestriction.equiv f (X →₀ FreeAlgebra R X) m)

theorem inclusion_augmentation_exact : Function.Exact (inclusion f) (augmentation f haug) := by
  intro a
  constructor
  · intro ha
    have hz : FreeAlgebra.algebraMapInv
        (AssociativeRestriction.equiv f (FreeAlgebra R X) a) = 0 :=
      congrArg (TrivialLieModule.equiv R L R) ha
    obtain ⟨m, hm⟩ := (FreeAugmentation.exact R X _).mp hz
    refine ⟨(AssociativeRestriction.equiv f (X →₀ FreeAlgebra R X)).symm m, ?_⟩
    apply (AssociativeRestriction.equiv f (FreeAlgebra R X)).injective
    exact hm
  · rintro ⟨m, rfl⟩
    exact congrArg (fun g : Generators f →ₗ⁅R,L⁆ Trivial R L => g m)
      (inclusion_augmentation_zero f haug)

theorem augmentation_surjective : Function.Surjective (augmentation f haug) := by
  intro r
  refine ⟨(AssociativeRestriction.equiv f (FreeAlgebra R X)).symm
    (algebraMap R (FreeAlgebra R X) (TrivialLieModule.equiv R L R r)), ?_⟩
  apply (TrivialLieModule.equiv R L R).injective
  exact FreeAlgebra.algebraMap_leftInverse _

/-- Removing the last letter retracts concatenation linearly. -/
def retraction : Regular f →ₗ[R] Generators f :=
  (AssociativeRestriction.equiv f (X →₀ FreeAlgebra R X)).symm.toLinearMap.comp
    ((FreeAugmentation.derivative R X).comp
      (AssociativeRestriction.equiv f (FreeAlgebra R X)).toLinearMap)

theorem retraction_inclusion : (retraction f).comp (inclusion f).toLinearMap = LinearMap.id := by
  ext m
  apply (AssociativeRestriction.equiv f (X →₀ FreeAlgebra R X)).injective
  exact FreeAugmentation.derivative_concatenate R X
    (AssociativeRestriction.equiv f (X →₀ FreeAlgebra R X) m)

/-- The restricted free associative augmentation sequence is short exact on
actual CE complexes, without an underlying-freeness hypothesis on the Lie algebra. -/
theorem sequence_shortExact :
    (sequence (inclusion f) (augmentation f haug) (inclusion_augmentation_zero f haug)).ShortExact :=
  sequence_shortExact_of_retraction (inclusion f) (augmentation f haug)
    (inclusion_augmentation_zero f haug) (inclusion_augmentation_exact f haug)
    (augmentation_surjective f haug) (retraction f) (retraction_inclusion f)

end Parafree.Homology.Coefficients.FreeAssociative
