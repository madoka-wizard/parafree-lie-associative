import Parafree.Homology.Coefficients.FoxExact
import Parafree.Homology.Coefficients.IdealCoinvariants
import Parafree.Homology.Coefficients.FamilyCoinvariants

/-! Explicit enveloping-algebra coordinates for the Fox relation sequence. -/

noncomputable section

namespace Parafree.Homology.Coefficients

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
theorem actionSpan_map_equiv (e : M ≃ₗ⁅R,L⁆ N) :
    (actionSpan R L M).map e.toLinearEquiv.toLinearMap = actionSpan R L N := by
  rw [actionSpan, Submodule.map_span, actionSpan]
  congr 1
  ext n
  constructor
  · rintro ⟨m, ⟨x, m, rfl⟩, rfl⟩
    exact ⟨x, e m, (e.map_lie x m).symm⟩
  · rintro ⟨x, n, rfl⟩
    refine ⟨⁅x,e.symm n⁆, ⟨x,e.symm n,rfl⟩, ?_⟩
    change e.toLieModuleHom ⁅x, e.symm n⁆ = ⁅x,n⁆
    rw [e.map_lie]
    exact congrArg (fun m => ⁅x,m⁆) (e.apply_symm_apply n)

def coinvariantsCongr (e : M ≃ₗ⁅R,L⁆ N) : Coinvariants R L M ≃ₗ[R] Coinvariants R L N :=
  Submodule.Quotient.equiv _ _ e.toLinearEquiv (actionSpan_map_equiv e)

omit [LieAlgebra R L] [LieModule R L M] [LieModule R L N] in
@[simp] theorem coinvariantsCongr_mk (e : M ≃ₗ⁅R,L⁆ N) (m : M) :
    coinvariantsCongr e (Submodule.Quotient.mk m) = Submodule.Quotient.mk (e m) := rfl

namespace FoxSequence

open Parafree.Associative
open FreeAssociative
open LieRings

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))

abbrev G := FreeLieAlgebra R X ⧸ J
abbrev U := UEA R (G R X J)

/-- The canonical map from the free associative algebra to the quotient enveloping algebra. -/
def projection : FreeAlgebra R X →ₐ[R] U R X J :=
  (UEA.mapToLieQuotient R (FreeLieAlgebra R X) J).comp
    (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X).symm.toAlgHom

@[simp] theorem projection_lie (x : FreeLieAlgebra R X) :
    projection R X J (PBW.freeLieToFreeAlgebra R X x) =
      UniversalEnvelopingAlgebra.ι R (LieSubmodule.Quotient.mk x : G R X J) := by
  have he : (FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X)
      (UniversalEnvelopingAlgebra.ι R x) = PBW.freeLieToFreeAlgebra R X x := by
    simp [FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra, PBW.freeLieToFreeAlgebra]
  rw [← he]
  change UEA.mapToLieQuotient R (FreeLieAlgebra R X) J
    ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X).symm
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X)
        (UniversalEnvelopingAlgebra.ι R x))) = _
  rw [AlgEquiv.symm_apply_apply, UEA.mapToLieQuotient_ι]

@[simp] theorem projection_ideal (j : J) : projection R X J (idealAction R X J j) = 0 := by
  change projection R X J (PBW.freeLieToFreeAlgebra R X (j : FreeLieAlgebra R X)) = 0
  rw [projection_lie, (LieSubmodule.Quotient.mk_eq_zero' (N := J)).mpr j.property, map_zero]

def regularCoordinates : Coinvariants R J (A R X J) ≃ₗ[R] U R X J :=
  (coinvariantsCongr (restrictedEnvelopingEquiv R X J).symm).trans
    (RelativeEnveloping.coinvariantsEquiv J)

@[simp] theorem regularCoordinates_mk (a : A R X J) :
    regularCoordinates R X J (Submodule.Quotient.mk a) =
      projection R X J (AssociativeRestriction.equiv (idealAction R X J) _ a) := by
  change (IdealCoinvariants.quotientEquiv J)
    (Submodule.Quotient.mk
      ((FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra R X).symm
        (AssociativeRestriction.equiv (idealAction R X J) _ a))) = _
  rfl

def coordinates : Q R X J ≃ₗ[R] (X →₀ U R X J) :=
  (AssociativeRestriction.familyCoinvariantsEquiv (idealAction R X J) X (FreeAlgebra R X)).trans
    (Finsupp.mapRange.linearEquiv (regularCoordinates R X J))

@[simp] theorem coordinates_mk_apply (b : B R X J) (x : X) :
    coordinates R X J (Submodule.Quotient.mk b) x =
      projection R X J (AssociativeRestriction.equiv (idealAction R X J) _ b x) := by
  change regularCoordinates R X J (Submodule.Quotient.mk
    ((AssociativeRestriction.familyLinear (idealAction R X J) X (FreeAlgebra R X)) b x)) = _
  rw [regularCoordinates_mk]
  rfl

/-- The explicit relation map in free quotient-enveloping coordinates. -/
def fox : LieRings.Homological.LieHomology.Abelianization R J →ₗ[R] (X →₀ U R X J) :=
  (coordinates R X J).toLinearMap.comp (relationMap R X J)

@[simp] theorem fox_mk_apply (j : J) (x : X) :
    fox R X J (Submodule.Quotient.mk j) x =
      projection R X J (FreeAugmentation.derivative R X (idealAction R X J j) x) :=
  coordinates_mk_apply R X J (derivative R X J j) x

theorem fox_injective [Module.Free R J] [Module.Free R (G R X J)] :
    Function.Injective (fox R X J) :=
  (coordinates R X J).injective.comp (relationMap_injective R X J)

/-- The expected last-letter multiplication map, over the quotient enveloping algebra. -/
def concatenate : (X →₀ U R X J) →ₗ[U R X J] U R X J :=
  Finsupp.linearCombination (U R X J)
    (fun x => projection R X J (FreeAlgebra.ι R x))

@[simp] theorem concatenate_single (x : X) (a : U R X J) :
    concatenate R X J (Finsupp.single x a) = a * projection R X J (FreeAlgebra.ι R x) :=
  Finsupp.linearCombination_single _ _ _

end FoxSequence
end Parafree.Homology.Coefficients
