import Parafree.Homology.Coefficients.FoxCoordinates

/-! Concrete multiplication and adjoint-action formulas for the relation sequence. -/

noncomputable section

namespace Parafree.Homology.Coefficients.FoxSequence

open Parafree.Associative
open FreeAssociative
open LieRings

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))

/-- Apply the enveloping quotient to every coefficient. -/
def familyProjection : (X →₀ FreeAlgebra R X) →ₗ[R] (X →₀ U R X J) :=
  Finsupp.mapRange.linearMap (projection R X J).toLinearMap

theorem coordinates_mk (b : B R X J) :
    coordinates R X J (Submodule.Quotient.mk b) =
      familyProjection R X J (AssociativeRestriction.equiv (idealAction R X J) _ b) := by
  ext x
  exact coordinates_mk_apply R X J b x

theorem projection_concatenate (b : X →₀ FreeAlgebra R X) :
    concatenate R X J (familyProjection R X J b) =
      projection R X J (FreeAugmentation.concatenate R X b) := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | single x a =>
    simp only [familyProjection, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
    rw [concatenate_single, FreeAugmentation.concatenate_single, map_mul]
    rfl

/-- The transported differential is ordinary multiplication, with no unspecified map. -/
theorem multiplication_coordinates (q : Q R X J) :
    concatenate R X J (coordinates R X J q) =
      regularCoordinates R X J (multiplication R X J q) := by
  obtain ⟨b,rfl⟩ := Submodule.mkQ_surjective (actionSpan R J (B R X J)) q
  change concatenate R X J (coordinates R X J (Submodule.Quotient.mk b)) =
    regularCoordinates R X J (multiplication R X J (Submodule.Quotient.mk b))
  rw [coordinates_mk, projection_concatenate, multiplication_mk, regularCoordinates_mk]
  rfl

/-- Exactness in actual quotient-enveloping coordinates. -/
theorem fox_exact : Function.Exact (fox R X J) (concatenate R X J) := by
  intro b
  constructor
  · intro hb
    have hq : multiplication R X J ((coordinates R X J).symm b) = 0 := by
      apply (regularCoordinates R X J).injective
      rw [← multiplication_coordinates, LinearEquiv.apply_symm_apply, hb, map_zero]
    obtain ⟨j,hj⟩ := (relationMap_exact R X J _).mp hq
    refine ⟨j, ?_⟩
    change coordinates R X J (relationMap R X J j) = b
    rw [hj, LinearEquiv.apply_symm_apply]
  · rintro ⟨j,rfl⟩
    change concatenate R X J (coordinates R X J (relationMap R X J j)) = 0
    rw [multiplication_coordinates,
      (relationMap_exact R X J _).mpr ⟨j,rfl⟩, map_zero]

/-- The ideal with its canonical ambient adjoint action. -/
def adjoint (x : FreeLieAlgebra R X) (j : J) : J := ⟨⁅x,(j : FreeLieAlgebra R X)⁆, J.lie_mem j.property⟩

/-- The Fox map carries the adjoint action to left multiplication by the quotient element. -/
theorem fox_adjoint (x : FreeLieAlgebra R X) (j : J) :
    fox R X J (Submodule.Quotient.mk (adjoint R X J x j)) =
      projection R X J (PBW.freeLieToFreeAlgebra R X x) •
        fox R X J (Submodule.Quotient.mk j) := by
  ext i
  rw [fox_mk_apply]
  change projection R X J
    (FreeAugmentation.derivative R X (PBW.freeLieToFreeAlgebra R X
      ⁅x,(j : FreeLieAlgebra R X)⁆) i) = _
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket,
    FreeAugmentation.derivative_commutator R X _ _
      (augmentation_freeLie R X x) (augmentation_freeLie R X j)]
  change projection R X J (PBW.freeLieToFreeAlgebra R X x *
      FreeAugmentation.derivative R X (idealAction R X J j) i -
        idealAction R X J j * FreeAugmentation.derivative R X
          (PBW.freeLieToFreeAlgebra R X x) i) =
    projection R X J (PBW.freeLieToFreeAlgebra R X x) *
      fox R X J (Submodule.Quotient.mk j) i
  rw [map_sub, map_mul, map_mul, projection_ideal, zero_mul, sub_zero, fox_mk_apply]

end Parafree.Homology.Coefficients.FoxSequence
