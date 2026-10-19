import Parafree.Homology.Coefficients.FreeLieIdeal
import Parafree.Homology.Coefficients.Coinvariants
import LieRings.Homological.LieHomology.LowDegreeHomology

/-!
# An explicit relation map, proved directly on low-degree CE chains

Last-letter differentiation gives the map on representatives. Its injectivity
is proved by filling a one-cycle in the already verified restricted regular
complex. Thus no representative computation for a categorical connecting
morphism is needed.
-/

noncomputable section

namespace Parafree.Homology.Coefficients.FoxSequence

open Parafree.Associative
open Parafree.Linear.ExteriorTensor
open FreeAssociative
open scoped TensorProduct

universe u
variable (R X : Type u) [CommRing R]
  (J : LieIdeal R (FreeLieAlgebra R X))

abbrev A := Regular (idealAction R X J)
abbrev B := Generators (idealAction R X J)
abbrev Q := Coinvariants R J (B R X J)

def derivative : J →ₗ[R] B R X J :=
  (AssociativeRestriction.equiv (idealAction R X J) (X →₀ FreeAlgebra R X)).symm.toLinearMap.comp
    ((FreeAugmentation.derivative R X).comp (idealAction R X J).toLinearMap)

def representative : J →ₗ[R] Q R X J :=
  (actionSpan R J (B R X J)).mkQ.comp (derivative R X J)

private theorem action_class_zero (j : J) (b : B R X J) :
    (Submodule.Quotient.mk ⁅j, b⁆ : Q R X J) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨j, b, rfl⟩)

theorem derivative_bracket (j k : J) :
    derivative R X J ⁅j, k⁆ = ⁅j, derivative R X J k⁆ - ⁅k, derivative R X J j⁆ := by
  change FreeAugmentation.derivative R X (idealAction R X J ⁅j,k⁆) = _
  rw [LieHom.map_lie, LieRing.of_associative_ring_bracket]
  exact FreeAugmentation.derivative_commutator R X _ _
    (augmentation_idealAction R X J j) (augmentation_idealAction R X J k)

theorem representative_bracket (j k : J) : representative R X J ⁅j,k⁆ = 0 := by
  change (actionSpan R J (B R X J)).mkQ (derivative R X J ⁅j,k⁆) = 0
  rw [derivative_bracket, map_sub]
  change (Submodule.Quotient.mk ⁅j, derivative R X J k⁆ : Q R X J) -
    Submodule.Quotient.mk ⁅k, derivative R X J j⁆ = 0
  rw [action_class_zero, action_class_zero, sub_self]

private theorem derived_le_ker :
    (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule ≤
      (representative R X J).ker := by
  intro j hj
  rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hj
  refine Submodule.span_induction (p := fun j _ => representative R X J j = 0)
    ?_ (map_zero _) ?_ ?_ hj
  · rintro j ⟨a, -, b, -, rfl⟩
    exact representative_bracket R X J a b
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  · intro r a _ ha
    rw [map_smul, ha, smul_zero]

/-- The positive last-letter derivative on the actual ideal abelianization. -/
def relationMap : LieRings.Homological.LieHomology.Abelianization R J →ₗ[R] Q R X J :=
  (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule.liftQ
    (representative R X J) (derived_le_ker R X J)

@[simp] theorem relationMap_mk (j : J) :
    relationMap R X J (Submodule.Quotient.mk j) = representative R X J j := rfl

/-- Apply augmentation to the coefficient of a one-chain. -/
def oneAugmentation : Chain R J (A R X J) 1 →ₗ[R] J :=
  (exteriorPower.oneEquiv R J).toLinearMap.comp
    ((trivialChainEquiv R J 1).toLinearMap.comp
      (chainMap (augmentation (idealAction R X J) (augmentation_idealAction R X J)) 1))

@[simp] theorem oneAugmentation_pure (j : J) (a : A R X J) :
    oneAugmentation R X J (pure R J (A R X J) 1 ![j] a) =
      FreeAlgebra.algebraMapInv (AssociativeRestriction.equiv (idealAction R X J) _ a) • j := by
  change exteriorPower.oneEquiv R J
    (FreeAlgebra.algebraMapInv (AssociativeRestriction.equiv (idealAction R X J) _ a) •
      exteriorPower.ιMulti R 1 ![j]) = _
  rw [map_smul, exteriorPower.oneEquiv_ιMulti]
  rfl

theorem oneAugmentation_boundary (c : Chain R J (A R X J) 2) :
    oneAugmentation R X J (differential R J (A R X J) 1 c) ∈
      (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule := by
  change exteriorPower.oneEquiv R J (trivialChainEquiv R J 1
    (chainMap (augmentation (idealAction R X J) (augmentation_idealAction R X J)) 1
      (differential R J (A R X J) 1 c))) ∈ _
  rw [chainMap_differential_apply, trivialChainEquiv_differential]
  change LieRings.Homological.LieHomology.degreeTwoBoundary R J _ ∈ _
  have h := LinearMap.mem_range_self (LieRings.Homological.LieHomology.degreeTwoBoundary R J)
    (trivialChainEquiv R J 2
      (chainMap (augmentation (idealAction R X J) (augmentation_idealAction R X J)) 2 c))
  rw [LieRings.Homological.LieHomology.range_degreeTwoBoundary R J] at h
  exact h

private theorem oneAugmentation_inclusion (c : Chain R J (B R X J) 1) :
    oneAugmentation R X J (chainMap (inclusion (idealAction R X J)) 1 c) = 0 := by
  induction c using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]; exact add_zero (0 : J)
  | tmul w b =>
    have hw : w = exteriorPower.ιMulti R 1 ![(exteriorPower.oneEquiv R J) w] := by
      apply (exteriorPower.oneEquiv R J).injective
      simp only [exteriorPower.oneEquiv_ιMulti]
      rfl
    rw [hw]
    change oneAugmentation R X J (pure R J (A R X J) 1
      ![(exteriorPower.oneEquiv R J) w] (inclusion (idealAction R X J) b)) = 0
    rw [oneAugmentation_pure]
    change FreeAlgebra.algebraMapInv (FreeAugmentation.concatenate R X _) • _ = 0
    rw [FreeAugmentation.augmentation_concatenate, zero_smul]; rfl

private theorem zeroChain_inclusion (c : Chain R J (B R X J) 0) :
    zeroChainEquiv R J (A R X J) (chainMap (inclusion (idealAction R X J)) 0 c) =
      inclusion (idealAction R X J) (zeroChainEquiv R J (B R X J) c) := by
  have hc : c = pure R J (B R X J) 0 ![] (zeroChainEquiv R J (B R X J) c) := by
    apply (zeroChainEquiv R J (B R X J)).injective
    rw [zeroChainEquiv_pure]
  conv_lhs => rw [hc]
  exact zeroChainEquiv_pure R J (A R X J) _

/-- A zero derivative class is a bracket boundary, by regular coefficient acyclicity. -/
theorem representative_eq_zero_iff [Module.Free R J]
    [Module.Free R (FreeLieAlgebra R X ⧸ J)] (j : J) :
    representative R X J j = 0 ↔
      j ∈ (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule := by
  constructor
  · intro hj
    have hm : derivative R X J j ∈ actionSpan R J (B R X J) :=
      (Submodule.Quotient.mk_eq_zero _).mp hj
    rw [← differential_zero_range_map R J (B R X J)] at hm
    obtain ⟨b, ⟨c, rfl⟩, hc⟩ := hm
    let z := pure R J (A R X J) 1 ![j]
      ((AssociativeRestriction.equiv (idealAction R X J) _).symm 1) +
        chainMap (inclusion (idealAction R X J)) 1 c
    have hz : differential R J (A R X J) 0 z = 0 := by
      apply (zeroChainEquiv R J (A R X J)).injective
      dsimp [z]
      rw [map_add, map_add, zeroChainEquiv_differential_pure,
        ← chainMap_differential_apply, zeroChain_inclusion, map_zero]
      erw [hc]
      change -(idealAction R X J j * 1) +
        FreeAugmentation.concatenate R X (FreeAugmentation.derivative R X (idealAction R X J j)) = 0
      rw [mul_one, FreeAugmentation.concatenate_derivative, augmentation_idealAction,
        map_zero, sub_zero, neg_add_cancel]
    obtain ⟨w, hw⟩ := (exactAt_succ_iff_fill (R := R) (L := J) (M := A R X J) 0).mp
      (ideal_regular_exactAt R X J 1 (by omega)) z hz
    have haug : oneAugmentation R X J z = j := by
      dsimp [z]
      rw [map_add, oneAugmentation_inclusion, oneAugmentation_pure]
      erw [add_zero]
      change FreeAlgebra.algebraMapInv (1 : FreeAlgebra R X) • j = j
      rw [map_one, one_smul]
    rw [← haug, ← hw]
    exact oneAugmentation_boundary R X J w
  · exact fun hj => derived_le_ker R X J hj

/-- Injectivity is proved for the explicit derivative, not only for an abstract connecting map. -/
theorem relationMap_injective [Module.Free R J]
    [Module.Free R (FreeLieAlgebra R X ⧸ J)] : Function.Injective (relationMap R X J) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨j, rfl⟩ := Submodule.mkQ_surjective
    (⁅(⊤ : LieIdeal R J), (⊤ : LieIdeal R J)⁆).toSubmodule a
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    ((representative_eq_zero_iff R X J j).mp ha)

end Parafree.Homology.Coefficients.FoxSequence
