import Parafree.TheoremA.DividedReduction
import Parafree.Lie.FreeHomogeneousLayers
import Parafree.Linear.QuotientReduction

/-! Concrete comparison of the positive reduced filtration layers with the
homogeneous components of the chosen integral free relation algebra. -/

noncomputable section
namespace Parafree.TheoremA.RationalModel

open Parafree.Lie Parafree.Linear
open Auxiliary

/-- Forget only the two nested subtype proofs in a lower-central term of the
relation ideal. Its image is precisely the corresponding divided-filtration term. -/
def relationTermEquiv (n : ℕ) :
    lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n ≃ₗ[ℤ] dividedFiltration (n + 1) :=
  Submodule.equivMapOfInjective (Auxiliary.relationIdeal ℤ).toSubmodule.subtype
    Subtype.val_injective (lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n).toSubmodule

@[simp] theorem relationTermEquiv_coe (n : ℕ)
    (x : lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n) :
    (relationTermEquiv n x : Auxiliary.Free ℤ) = (x : Auxiliary.relationIdeal ℤ) := rfl

abbrev integralLayerRelations (n : ℕ) : Submodule ℤ (dividedFiltration n) :=
  (dividedFiltration (n + 1)).comap (dividedFiltration n).subtype

abbrev IntegralLayer (n : ℕ) := dividedFiltration n ⧸ integralLayerRelations n

theorem relationTerm_next_iff (n : ℕ) (x : lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n) :
    relationTermEquiv n x ∈ integralLayerRelations (n + 1) ↔
      x ∈ layerRelations ℤ (Auxiliary.relationIdeal ℤ) n := by
  change ((x : Auxiliary.relationIdeal ℤ) : Auxiliary.Free ℤ) ∈ dividedFiltration (n + 1 + 1) ↔
    (x : Auxiliary.relationIdeal ℤ) ∈ lowerCentral ℤ (Auxiliary.relationIdeal ℤ) (n + 1)
  rw [mem_dividedFiltration_succ]
  constructor
  · rintro ⟨hx, h⟩
    exact h
  · intro h
    exact ⟨(x : Auxiliary.relationIdeal ℤ).property, h⟩

def relationLayerPresentation (n : ℕ) :
    lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n →ₗ[ℤ] IntegralLayer (n + 1) :=
  (integralLayerRelations (n + 1)).mkQ.comp (relationTermEquiv n).toLinearMap

theorem relationLayerPresentation_surjective (n : ℕ) :
    Function.Surjective (relationLayerPresentation n) :=
  (integralLayerRelations (n + 1)).mkQ_surjective.comp (relationTermEquiv n).surjective

theorem relationLayerPresentation_ker (n : ℕ) :
    LinearMap.ker (relationLayerPresentation n) = layerRelations ℤ (Auxiliary.relationIdeal ℤ) n := by
  ext x
  change (integralLayerRelations (n + 1)).mkQ (relationTermEquiv n x) = 0 ↔ _
  exact (Submodule.Quotient.mk_eq_zero (integralLayerRelations (n + 1))).trans
    (relationTerm_next_iff n x)

/-- The comparison with the actual embedded filtration, before reduction. -/
def embeddedRelationLayerEquiv (n : ℕ) :
    LowerCentralLayer ℤ (Auxiliary.relationIdeal ℤ) n ≃ₗ[ℤ] IntegralLayer (n + 1) :=
  equivOfCommonPresentation (layerRelations ℤ (Auxiliary.relationIdeal ℤ) n).mkQ
    (relationLayerPresentation n) (Submodule.mkQ_surjective _)
    (relationLayerPresentation_surjective n)
    ((Submodule.ker_mkQ _).trans (relationLayerPresentation_ker n).symm)

theorem embeddedRelationLayerEquiv_mk (n : ℕ)
    (x : lowerCentral ℤ (Auxiliary.relationIdeal ℤ) n) :
    embeddedRelationLayerEquiv n (Submodule.Quotient.mk x) =
      (integralLayerRelations (n + 1)).mkQ (relationTermEquiv n x) :=
  equivOfCommonPresentation_apply _ _ _ _ _ x

/-- Integral homogeneous components map to the actual filtration by the already
specified lift of the relation-module basis. -/
def homogeneousIntegralLayerEquiv (n : ℕ) :
    FreeHomogeneous.component RelationBasisIndex (n + 1) ≃ₗ[ℤ] IntegralLayer (n + 1) :=
  ((FreeHomogeneous.layerEquiv RelationBasisIndex n).trans (relationLayerEquiv n)).trans
    (embeddedRelationLayerEquiv n)

def homogeneousRelationTerm (n : ℕ) :
    FreeHomogeneous.component RelationBasisIndex (n + 1) →ₗ[ℤ] dividedFiltration (n + 1) :=
  (relationTermEquiv n).toLinearMap.comp ((lowerCentralRestriction relationFreeMap n).comp
    ((FreeHomogeneous.component RelationBasisIndex (n + 1)).subtype.codRestrict _
      (FreeHomogeneous.component_mem_lowerCentral RelationBasisIndex n)))

theorem homogeneousIntegralLayerEquiv_apply (n : ℕ)
    (x : FreeHomogeneous.component RelationBasisIndex (n + 1)) :
    homogeneousIntegralLayerEquiv n x =
      (integralLayerRelations (n + 1)).mkQ (homogeneousRelationTerm n x) := by
  change embeddedRelationLayerEquiv n
    (relationLayerEquiv n (FreeHomogeneous.layerEquiv RelationBasisIndex n x)) = _
  rw [FreeHomogeneous.layerEquiv_apply, relationLayerEquiv_mk, embeddedRelationLayerEquiv_mk]
  rfl

/-- Each positive layer is the reduction of a homogeneous free-Lie component. -/
def positiveLayerEquiv (n : ℕ) :
    ModScalar.Quotient (2 : ℤ) (FreeHomogeneous.component RelationBasisIndex (n + 1)) ≃ₗ[ℤ]
      ReducedLayer (n + 1) :=
  (ModScalar.congr (2 : ℤ) (homogeneousIntegralLayerEquiv n)).trans
    (ModScalar.quotientReductionEquiv (2 : ℤ) (integralLayerRelations (n + 1)))

theorem positiveLayerEquiv_mk (n : ℕ)
    (x : FreeHomogeneous.component RelationBasisIndex (n + 1)) :
    positiveLayerEquiv n (ModScalar.mk (2 : ℤ) _ x) =
      (reducedLayerRelations (n + 1)).mkQ (homogeneousRelationTerm n x) := by
  change ModScalar.quotientReductionEquiv (2 : ℤ) (integralLayerRelations (n + 1))
    (ModScalar.mk (2 : ℤ) _ (homogeneousIntegralLayerEquiv n x)) = _
  rw [homogeneousIntegralLayerEquiv_apply, ModScalar.quotientReductionEquiv_mk]
  rfl

attribute [irreducible] positiveLayerEquiv homogeneousIntegralLayerEquiv embeddedRelationLayerEquiv

end Parafree.TheoremA.RationalModel
