import Parafree.TheoremA.RelationIdeal
import Parafree.Lie.FreeTruncation
import Parafree.Lie.LowerCentralLayers

/-! The specific countable free source for the relation-ideal filtration.
This supplies the chosen map, its natural lower-central comparison, and
freeness of the actual relation ideal's nilpotent quotients. -/

noncomputable section

namespace Parafree.TheoremA.Auxiliary

abbrev RelationAbelianization :=
  LieRings.Homological.LieHomology.Abelianization ℤ (relationIdeal ℤ)

abbrev RelationBasisIndex := Module.Free.ChooseBasisIndex ℤ RelationAbelianization

def relationBasis : Module.Basis RelationBasisIndex ℤ RelationAbelianization :=
  Module.Free.chooseBasis ℤ RelationAbelianization

instance relationBasisIndex_countable : Countable RelationBasisIndex := by
  letI : Countable (Parafree.Homology.Coefficients.FoxSequence.U ℤ (Fin 3) (relationIdeal ℤ)) :=
    (envelopingBasis ℤ).repr.injective.countable
  letI : Countable RelationAbelianization :=
    (@Parafree.Homology.Coefficients.FoxSequence.fox_injective
      ℤ (Fin 3) _ (relationIdeal ℤ) relationIdeal_free (presented_free ℤ)).countable
  exact relationBasis.injective.countable

private abbrev derivedRelation :=
  (⁅(⊤ : LieIdeal ℤ (relationIdeal ℤ)), (⊤ : LieIdeal ℤ (relationIdeal ℤ))⁆).toSubmodule

/-- Chosen lifts of a basis of the actual integral relation module. -/
def relationBasisLift (i : RelationBasisIndex) : relationIdeal ℤ :=
  (Submodule.mkQ_surjective derivedRelation (relationBasis i)).choose

@[simp] theorem relationBasisLift_class (i : RelationBasisIndex) :
    (Submodule.Quotient.mk (relationBasisLift i) : RelationAbelianization) = relationBasis i :=
  (Submodule.mkQ_surjective derivedRelation (relationBasis i)).choose_spec

abbrev RelationFree := FreeLieAlgebra ℤ RelationBasisIndex

/-- The map obtained by lifting the chosen basis of the actual abelianization. -/
def relationFreeMap : RelationFree →ₗ⁅ℤ⁆ relationIdeal ℤ :=
  FreeLieAlgebra.lift ℤ relationBasisLift

@[simp] theorem relationFreeMap_of (i : RelationBasisIndex) :
    relationFreeMap (FreeLieAlgebra.of ℤ i) = relationBasisLift i :=
  FreeLieAlgebra.lift_of_apply _ _

/-- Freeness at every finite stage, despite the possibly infinite basis. -/
theorem relationFree_nilpotent_free (n : ℕ) :
    Module.Free ℤ (RelationFree ⧸ Parafree.Lie.lowerCentral ℤ RelationFree n) :=
  Parafree.Lie.FreeTruncation.quotient_free RelationBasisIndex n

open Parafree.Lie

/-- The inverse on abelianizations, defined on the chosen basis. -/
def relationAbelianInverse :
    (relationIdeal ℤ ⧸ lowerCentral ℤ (relationIdeal ℤ) 1) →ₗ⁅ℤ⁆
      (RelationFree ⧸ lowerCentral ℤ RelationFree 1) :=
  { relationBasis.constr ℤ (fun i => quotientMk _ (FreeLieAlgebra.of ℤ i)) with
    map_lie' := by
      intro x y
      rw [lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1) x y,
        lie_eq_zero_of_lowerCentral_one (lowerCentral_quotient_eq_bot 1)]
      exact (relationBasis.constr ℤ (fun i => quotientMk _ (FreeLieAlgebra.of ℤ i))).map_zero }

@[simp] theorem relationAbelianInverse_basis (i : RelationBasisIndex) :
    relationAbelianInverse (relationBasis i) = quotientMk _ (FreeLieAlgebra.of ℤ i) :=
  relationBasis.constr_basis ℤ _ i

/-- The selected map, rather than an abstract replacement, is an isomorphism
on abelianizations. -/
theorem relationFreeMap_abelian_bijective :
    Function.Bijective (nilpotentMap relationFreeMap 1) := by
  have hleft : relationAbelianInverse.comp (nilpotentMap relationFreeMap 1) =
      LieHom.id := by
    apply quotient_hom_ext
    apply FreeLieAlgebra.hom_ext
    intro i
    change relationAbelianInverse (quotientMk _ (relationFreeMap (FreeLieAlgebra.of ℤ i))) = _
    rw [relationFreeMap_of]
    have hi : quotientMk (lowerCentral ℤ (relationIdeal ℤ) 1) (relationBasisLift i) =
        relationBasis i := relationBasisLift_class i
    rw [hi, relationAbelianInverse_basis]
    rfl
  have hright : (nilpotentMap relationFreeMap 1).comp relationAbelianInverse =
      LieHom.id := by
    apply LieHom.ext
    have hlinear : (nilpotentMap relationFreeMap 1).toLinearMap.comp
        relationAbelianInverse.toLinearMap = LinearMap.id := by
      apply relationBasis.ext
      intro i
      change nilpotentMap relationFreeMap 1 (relationAbelianInverse (relationBasis i)) = _
      rw [relationAbelianInverse_basis, nilpotentMap_mk, relationFreeMap_of]
      exact relationBasisLift_class i
    exact LinearMap.congr_fun hlinear
  exact ⟨(fun x y h => by
    exact (LieHom.congr_fun hleft x).symm.trans
      ((congrArg relationAbelianInverse h).trans (LieHom.congr_fun hleft y))),
    fun y => ⟨relationAbelianInverse y, LieHom.congr_fun hright y⟩⟩

/-- The chosen free map induces isomorphisms at every lower-central stage. -/
theorem relationFreeMap_isParaEquivalence : IsParaEquivalence relationFreeMap := by
  letI := relationIdeal_homology_subsingleton 0
  exact isParaEquivalence_of_homologyTwo_zero relationFreeMap relationFreeMap_abelian_bijective

/-- Freeness of the actual integral relation ideal's finite nilpotent quotients. -/
theorem relationIdeal_nilpotent_free (n : ℕ) :
    Module.Free ℤ (relationIdeal ℤ ⧸ lowerCentral ℤ (relationIdeal ℤ) n) := by
  exact Module.Free.of_equiv' (relationFree_nilpotent_free n)
    (LieEquiv.ofBijective (nilpotentMap relationFreeMap n)
      (relationFreeMap_isParaEquivalence n)).toLinearEquiv

/-- The specified lifted map induces the comparison on every successive layer. -/
def relationLayerEquiv (n : ℕ) :
    LowerCentralLayer ℤ RelationFree n ≃ₗ[ℤ]
      LowerCentralLayer ℤ (relationIdeal ℤ) n :=
  relationFreeMap_isParaEquivalence.layerEquiv n

@[simp] theorem relationLayerEquiv_mk (n : ℕ) (x : lowerCentral ℤ RelationFree n) :
    relationLayerEquiv n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (lowerCentralRestriction relationFreeMap n x) := rfl

end Parafree.TheoremA.Auxiliary
