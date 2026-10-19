import Parafree.Homology.Coefficients.FoxEquivariance

/-! The canonical relation coefficients and their actual dimension shift.
The relation module is represented by the kernel of multiplication, with its
quotient-enveloping action. `relationEquiv` identifies its underlying module
with the actual ideal abelianization; `relationEquiv_adjoint` identifies the
action on representatives. -/

noncomputable section

namespace Parafree.Homology.Coefficients.FoxSequence

open Parafree.Associative
open FreeAssociative
open LieRings

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))

@[simp] theorem projection_generator (x : X) :
    projection R X J (FreeAlgebra.ι R x) =
      UniversalEnvelopingAlgebra.ι R
        (LieSubmodule.Quotient.mk (FreeLieAlgebra.of R x) : G R X J) := by
  simpa only [PBW.freeLieToFreeAlgebra, FreeLieAlgebra.lift_of_apply] using
    projection_lie R X J (FreeLieAlgebra.of R x)

theorem projection_surjective : Function.Surjective (projection R X J) := by
  intro a
  obtain ⟨q,hq⟩ := (regularCoordinates R X J).surjective a
  obtain ⟨b,rfl⟩ := Submodule.mkQ_surjective (actionSpan R J (A R X J)) q
  exact ⟨AssociativeRestriction.equiv (idealAction R X J) _ b,
    (regularCoordinates_mk R X J b).symm.trans hq⟩

@[simp] theorem augmentation_projection (a : FreeAlgebra R X) :
    UEA.augmentation R (G R X J) (projection R X J a) = FreeAlgebra.algebraMapInv a := by
  have h : (UEA.augmentation R (G R X J)).comp (projection R X J) =
      FreeAlgebra.algebraMapInv := by
    apply FreeAlgebra.hom_ext
    funext x
    change UEA.augmentation R (G R X J) (projection R X J (FreeAlgebra.ι R x)) = _
    rw [projection_generator, UEA.augmentation_ι]
    simp [FreeAlgebra.algebraMapInv]
  exact AlgHom.congr_fun h a

theorem concatenate_augmentation (b : X →₀ U R X J) :
    UEA.augmentation R (G R X J) (concatenate R X J b) = 0 := by
  induction b using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single x a => rw [concatenate_single, map_mul, projection_generator, UEA.augmentation_ι, mul_zero]

abbrev FreeCoefficients := AssociativeRestriction.Coefficients
  (UniversalEnvelopingAlgebra.ι R : G R X J →ₗ⁅R⁆ U R X J) (X →₀ U R X J)

def freeCoordinates : FreeCoefficients R X J ≃ₗ[R] (X →₀ U R X J) :=
  AssociativeRestriction.equiv _ _

/-- Multiplication as a homomorphism of quotient-Lie coefficient modules. -/
def coefficientMultiplication : FreeCoefficients R X J →ₗ⁅R,G R X J⁆
    Enveloping.Regular R (G R X J) :=
  { (Enveloping.equiv R (G R X J)).symm.toLinearMap.comp
      (((concatenate R X J).restrictScalars R).comp (freeCoordinates R X J).toLinearMap) with
    map_lie' := by
      intro x b
      apply (Enveloping.equiv R (G R X J)).injective
      change concatenate R X J (UniversalEnvelopingAlgebra.ι R x • freeCoordinates R X J b) =
        UniversalEnvelopingAlgebra.ι R x * concatenate R X J (freeCoordinates R X J b)
      exact (concatenate R X J).map_smul _ _ }

def relations : LieSubmodule R (G R X J) (FreeCoefficients R X J) :=
  (coefficientMultiplication R X J).ker

/-- The canonical relation module, including the quotient Lie action. -/
abbrev RelationCoefficients := relations R X J

def toAugmentation : FreeCoefficients R X J →ₗ⁅R,G R X J⁆ Enveloping.ideal R (G R X J) :=
  (coefficientMultiplication R X J).codRestrict _ (fun b => by
    apply (TrivialLieModule.equiv R (G R X J) R).injective
    change UEA.augmentation R (G R X J) (concatenate R X J (freeCoordinates R X J b)) = 0
    exact concatenate_augmentation R X J _)

theorem toAugmentation_surjective : Function.Surjective (toAugmentation R X J) := by
  intro a
  obtain ⟨b,hb⟩ := projection_surjective R X J (Enveloping.equiv R (G R X J) a)
  have haug : FreeAlgebra.algebraMapInv b = 0 := by
    rw [← augmentation_projection R X J b, hb]
    exact congrArg (TrivialLieModule.equiv R (G R X J) R) a.property
  refine ⟨(freeCoordinates R X J).symm
    (familyProjection R X J (FreeAugmentation.derivative R X b)), ?_⟩
  apply Subtype.ext
  apply (Enveloping.equiv R (G R X J)).injective
  change concatenate R X J (familyProjection R X J (FreeAugmentation.derivative R X b)) = _
  rw [projection_concatenate, FreeAugmentation.concatenate_derivative, haug, map_zero, sub_zero, hb]

theorem relation_sequence_zero : (toAugmentation R X J).comp (relations R X J).incl = 0 := by
  ext b
  exact b.property

theorem relation_sequence_exact : Function.Exact (relations R X J).incl (toAugmentation R X J) := by
  intro b
  constructor
  · intro hb
    exact ⟨⟨b, congrArg Subtype.val hb⟩, rfl⟩
  · rintro ⟨b,rfl⟩
    apply Subtype.ext
    exact b.property

/-- The explicit relation sequence is short exact on the actual coefficient CE complexes. -/
theorem relation_sequence_shortExact [Module.Free R (G R X J)] :
    (sequence (relations R X J).incl (toAugmentation R X J) (relation_sequence_zero R X J)).ShortExact :=
  sequence_shortExact_of_free _ _ (relation_sequence_zero R X J)
    (relation_sequence_exact R X J) (Subtype.val_injective) (toAugmentation_surjective R X J)

/-- The actual abelianized ideal in the canonical kernel model. -/
def relationMapToKernel : LieRings.Homological.LieHomology.Abelianization R J →ₗ[R]
    RelationCoefficients R X J :=
  ((freeCoordinates R X J).symm.toLinearMap.comp (fox R X J)).codRestrict _ (fun a => by
    apply (Enveloping.equiv R (G R X J)).injective
    change concatenate R X J (fox R X J a) = 0
    exact (fox_exact R X J _).mpr ⟨a,rfl⟩)

def relationEquiv [Module.Free R J] [Module.Free R (G R X J)] :
    LieRings.Homological.LieHomology.Abelianization R J ≃ₗ[R] RelationCoefficients R X J :=
  LinearEquiv.ofBijective (relationMapToKernel R X J) ⟨by
    intro a b hab
    apply fox_injective R X J
    exact congrArg (fun c : RelationCoefficients R X J => freeCoordinates R X J c) hab,
    by
      intro b
      have hb : concatenate R X J (freeCoordinates R X J b) = 0 :=
        congrArg (Enveloping.equiv R (G R X J)) b.property
      obtain ⟨a,ha⟩ := (fox_exact R X J _).mp hb
      refine ⟨a, ?_⟩
      apply Subtype.ext
      apply (freeCoordinates R X J).injective
      exact ha⟩

/-- The action in the kernel model is the adjoint action on the ideal's abelianization. -/
theorem relationEquiv_adjoint [Module.Free R J] [Module.Free R (G R X J)]
    (x : FreeLieAlgebra R X) (j : J) :
    relationEquiv R X J (Submodule.Quotient.mk (adjoint R X J x j)) =
      ⁅(LieSubmodule.Quotient.mk x : G R X J), relationEquiv R X J (Submodule.Quotient.mk j)⁆ := by
  apply Subtype.ext
  apply (freeCoordinates R X J).injective
  change fox R X J (Submodule.Quotient.mk (adjoint R X J x j)) =
    UniversalEnvelopingAlgebra.ι R (LieSubmodule.Quotient.mk x : G R X J) •
      fox R X J (Submodule.Quotient.mk j)
  rw [fox_adjoint, projection_lie]

private def regularEquiv :
    AssociativeRestriction.Coefficients (UniversalEnvelopingAlgebra.ι R : G R X J →ₗ⁅R⁆ U R X J)
      (U R X J) ≃ₗ⁅R,G R X J⁆ Enveloping.Regular R (G R X J) :=
  { (AssociativeRestriction.equiv _ _).trans (Enveloping.equiv R (G R X J)).symm with
    map_lie' := by intros; rfl }

private theorem freeCoefficients_homology_isZero [Module.Free R (G R X J)] (n : ℕ) (hn : n ≠ 0) :
    CategoryTheory.Limits.IsZero (homology R (G R X J) (FreeCoefficients R X J) n) := by
  classical
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
  apply exactAt_of_equiv (AssociativeRestriction.finsuppEquiv
    (UniversalEnvelopingAlgebra.ι R : G R X J →ₗ⁅R⁆ U R X J) X (U R X J)) n hn
  exact DirectSums.exactAt R (G R X J) _ n hn (fun _ =>
    exactAt_of_equiv (regularEquiv R X J) n hn (Enveloping.exactAt R (G R X J) n hn))

/-- Two dimension shifts for the concrete relation coefficients, with no exactness hypotheses. -/
def relationHomologyEquiv [Module.Free R (G R X J)] (n : ℕ) (hn : n ≠ 0) :
    Homology R (G R X J) (RelationCoefficients R X J) n ≃ₗ[R]
      LieRings.Homological.LieHomology.Homology (R := R) (L := G R X J) (n + 2) :=
  (dimensionShift (relation_sequence_shortExact R X J) n
    (freeCoefficients_homology_isZero R X J (n + 1) (by omega))
    (freeCoefficients_homology_isZero R X J n hn)).symm.trans
      (Enveloping.augmentationHomologyEquiv R (G R X J) n)

end Parafree.Homology.Coefficients.FoxSequence
